
# packages

library(remotes)
library(tidyverse)
library(lubridate)
library(data.table)

library(forecast)
library(dlm)
library(tseries)
library(rugarch)
library(broom)

library(PerformanceAnalytics)
library(CVXR)

library(glue)
library(ggplot2)
library(gt)
library(futile.logger)

# parameters

rolling_window_lengths <- c(252)
horizon_lengths <- c(21)
kappa <- 0.0005

# knitting options

knitr::opts_chunk$set(
    error = FALSE,
    warning = FALSE,
    message = FALSE,
    echo = TRUE,
    fig.width = 9,
    fig.height = 6,
    fig.align = 'center'
)

# plot options

theme_set(theme_bw())

# simple functions

nan_sum <- purrr::partial(sum, na.rm = TRUE)
nan_mean <- purrr::partial(mean, na.rm = TRUE)
nan_sd <- purrr::partial(sd, na.rm = TRUE)
nan_var <- purrr::partial(var, na.rm = TRUE)
nan_cumsum <- function(x) cumsum(ifelse(is.na(x), 0, x))

# read 

read_short_history <- function() {
    fread('data/short_history/history_60d.csv') %>%
        .[, date := as.Date(date)] %>%
        .[, list(symbol, date, adjclose, volume)] %>%
        setkey(symbol, date) %>%
        setindex(date)
}


read_single_table <- function(path) {
    flog.info(glue("reading {path}..."))
    fread(path) %>%
        .[, date := as.Date(date)] %>%
        .[date >= max(date, na.rm = TRUE) - years(10)]
}

read_partial_history <- function() {
    list.files("data/partial_history", pattern = "*.csv", full.names = TRUE) %>%
        set_names(., list.files("data/partial_history", pattern = "*.csv", full.names = FALSE) %>% gsub(".csv", "", .)) %>%
        lapply(read_single_table) %>%
        rbindlist(use.names = TRUE, fill = TRUE, idcol = 'symbol') %>%
        .[, list(symbol, date, adjclose, volume)] %>%
        setkey(symbol, date) %>%
        setindex(date)
}

read_full_history <- function() {
    list.files("data/full_history/", pattern = "*.csv", full.names = TRUE) %>%
        set_names(., list.files("data/full_history", pattern = "*.csv", full.names = FALSE) %>% gsub(".csv", "", .)) %>%
        lapply(read_single_table) %>%
        rbindlist(use.names = TRUE, fill = TRUE, idcol = 'symbol') %>%
        .[, list(symbol, date, adjclose, volume)] %>%
        setkey(symbol, date) %>%
        setindex(date)
}

read_sp <- function() {
    fread('data/sp/SP500new.csv') %>%
        .[j = list(date = Date, close = Close)] %>%
        .[, date := as.Date(date)] %>%
        setkey(date) %>%
        .[, symbol := "S&P"] %>%
        .[, log_return := log(close) - log(shift(close))] %>%
        .[, portfolio_method := 'S&P Benchmark'] %>%
        .[, weight := 1] %>%
        .[, lagged_weight := 1] %>%
        .[, drifted_weight := 1]
}

# data and universe

define_universe <- function(df_raw) {
    
    max_consecutive_missing <- function(df) {
        nan_max <- function(x) ifelse(is.null(x), 0, max(x, na.rm = TRUE)) %>% as.double %>% ifelse(. == -Inf, 0, .)
        run_lengths <- rle(!complete.cases(df))
        consecutive_missing <- run_lengths$lengths[run_lengths$values == TRUE]
        m <- nan_max(consecutive_missing)
        return(m)
    }
    
    # filter date
    df_universe <- df_raw %>%
        copy() %>%
        .[date >= max(date) - years(10)]
    
    # cross join on all symbol x date pairs
    df_universe <- df_universe %>%
        merge(df_universe[, CJ(symbol, date, unique = TRUE, sorted = TRUE)], by = c("symbol", "date"), all = TRUE)
    
    # compute missing statistics
    df_missing <- df_universe %>%
        .[
            j = list(
                count_missing = sum(!complete.cases(.SD)),
                percentage_missing = sum(!complete.cases(.SD)) / .N,
                max_consecutive_missing = max_consecutive_missing(.SD),
                mdtv = median(volume * adjclose, na.rm = TRUE),
            ),
            keyby = symbol
            ] %>%
        .[order(percentage_missing, decreasing = TRUE)] 
    
    # filter based on missing statistics
    df_universe <- df_universe %>%
        merge(df_missing, by = "symbol", all.x = TRUE, all.y = FALSE) %>%
        .[percentage_missing <= 0.05] %>%
        .[max_consecutive_missing <= 4] %>%
        .[mdtv >= 10000000]
    
    return(df_universe)
}

clean_universe <- function(df_universe) {
    
    clip_returns <- function(r, lower, upper) {
        pmax(lower, pmin(r, upper))
    }
    
    different_or_missing <- function(x, y) {
        ((x != y) | (is.na(x) & !is.na(y)) | (is.na(y) & !is.na(x)))
    }
    
    df_clean <- df_universe %>% 
        copy() %>%
        .[, clean_adjclose := na.interp(adjclose, linear = TRUE) %>% as.numeric(), by = symbol] %>%
        .[, percentage_return := adjclose / shift(adjclose) - 1, by = symbol] %>%
        .[, log_return := base::log(clean_adjclose) - base::log(data.table::shift(clean_adjclose)), by = symbol] %>%
        .[, clean_log_return := clip_returns(log_return, -1, 1)] %>%
        .[, is_cleaned_adjclose := different_or_missing(clean_adjclose, adjclose) %>% coalesce(FALSE)] %>%
        .[, is_cleaned_log_return := different_or_missing(clean_log_return, log_return) %>% coalesce(FALSE)] %>%
        .[, has_adjclose_outlier := any(is_cleaned_adjclose), by = symbol] %>%
        .[, has_log_return_outlier := any(is_cleaned_log_return), by = symbol]
    
    df_dirty <- df_clean %>%
        .[j = list(too_many_large_returns = (nan_sum(abs(percentage_return) >= 0.05) / .N) >= 0.10), keyby = symbol] %>%
        .[too_many_large_returns == TRUE]
    
    df_duplicated <- df_clean %>%
        .[, .N, by = list(symbol, date)] %>%
        .[N != 1] %>%
        .[, is_duplicated := TRUE]
    
    df_clean <- df_clean %>%
        .[!(symbol %in% unique(df_dirty$symbol))] %>%
        .[!(symbol %in% unique(df_duplicated$symbol))] 
        
    return(df_clean)
}

# signals

estimate_simple <- function(df) {
    
    estimate_mean <- function(r) 0.99 * (0.04 / 252) + 0.01 * nan_mean(r)
    estimate_vol <- function(r) nan_sd(r)
    estimate_sharpe <- function(r) estimate_mean(r) / estimate_vol(r)
    estimate_beta <- function(r, m) cov(r, m, use = "pairwise.complete.obs") / nan_var(m)

    df_estimated <- df %>%
        .[
            j = list(
                estimated_start_date = min(date),
                estimated_end_date = max(date),
                estimated_mean = 252 * estimate_mean(clean_log_return),
                estimated_vol = sqrt(252) * estimate_vol(clean_log_return),
                estimated_sharpe = sqrt(252) * estimate_sharpe(clean_log_return),
                estimated_beta = estimate_beta(clean_log_return, market_log_return)
            ),
            keyby = symbol
        ]   

    df_estimated_epsilon <- df %>%
        merge(df_estimated, by = "symbol", all.x = TRUE, all.y = FALSE) %>% 
        .[, epsilon_log_return := clean_log_return - estimated_beta * market_log_return] %>%
        .[
            j = list(
                estimated_market_vol = sqrt(252) * estimate_vol(market_log_return),
                estimated_epsilon_vol = sqrt(252) * estimate_vol(epsilon_log_return)
            ),
            keyby = symbol
            ]
    
    df_estimated <- df_estimated %>%
        merge(df_estimated_epsilon, by = "symbol", all.x = TRUE, all.y = FALSE)
    
    return(df_estimated)
}

prepare_market_returns <- function(df_clean) {
    
    flog.info(glue("preparing market weights..."))
    
    df_stocks <- df_clean %>%
        .[j = list(symbol, date, adjclose, clean_adjclose, log_return, clean_log_return, volume)] %>%
        .[, market_weight := 1 / .N, by = date] %>%
        .[, log_dtv := log(clean_adjclose * volume)] %>%
        .[, size := rollmean(log_dtv, k = 250, align = "right", fill = NA), by = symbol] %>%
        .[, size_percent_rank := size %>% percent_rank(), by = date] %>%
        .[, size_weight := case_when(size_percent_rank <= 0.30 ~ 1, size_percent_rank >= 0.70 ~ -1, TRUE ~ 0)] %>%
        .[, momentum := rollmean(clean_log_return %>% shift(30), k = 250, align = "right", fill = NA), by = symbol] %>%
        .[, momentum_percent_rank := momentum %>% percent_rank(), by = date] %>%
        .[, momentum_weight := case_when(momentum_percent_rank <= 0.30 ~ -1, momentum_percent_rank >= 0.70 ~ 1, TRUE ~ 0)]    
    
    df_stocks <- df_stocks %>%
        .[, market_weight := market_weight / nan_sum(abs(market_weight)), by = date] %>%
        .[, size_weight := size_weight / nan_sum(abs(size_weight)), by = date] %>%
        .[, momentum_weight := momentum_weight / nan_sum(abs(momentum_weight)), by = date]
        
    flog.info(glue("preparing market returns..."))
    
    df_market <- df_stocks %>%
        .[
            i = !is.na(market_weight) & !is.na(size_weight) & !is.na(momentum_weight),
            j = list(
                market_log_return = nan_sum(market_weight * clean_log_return),
                size_log_return = nan_sum(size_weight * clean_log_return),
                momentum_log_return = nan_sum(momentum_weight * clean_log_return)
            ),
            keyby = date
            ]
    
    flog.info(glue("storing market returns..."))
    
    df_stocks <- df_stocks %>%
        merge(df_market, by = "date", all.x = TRUE, all.y = FALSE)
    
    return(df_stocks)
}

estimation_factor_model <- function(df_data) {

    start_date <- df_data[, min(date)]
    end_date <- df_data[, max(date)]
    
    df_stocks <- df_data %>%
        copy() 

    df_stocks <- df_stocks %>%
        .[complete.cases(clean_log_return, market_log_return, size_log_return, momentum_log_return)] %>%
        setkey(symbol, date) %>%
        setindex(date)
    
    if (nrow(df_stocks) == 0) {
        return(NULL)
    }    
    
    # fama french betas
    
    flog.info(glue("    estimating fama french first stage for {end_date}..."))
    
    convert_betas_to_loadings <- function(betas) {
        2 * percent_rank(betas) - 1
    }
    
    df_fama_french_betas <- df_stocks %>%
        .[
            j = tidy(lm(clean_log_return ~ market_log_return + size_log_return + momentum_log_return)),
            keyby = list(symbol)
            ] %>%
        .[term != "(Intercept)"] %>%
        .[, term := gsub("_log_return", "_factor_beta", term)] %>%
        .[term == "market_factor_beta", factor_beta := pmax(0, pmin(estimate, 3))] %>%
        .[term != "market_factor_beta", factor_beta := pmax(-3, pmin(estimate, 3))] %>%
        .[, factor_tstat := statistic] %>%
        .[, j = list(symbol, term, factor_beta, factor_tstat)] %>%
        setkey(symbol, term)
    
    df_fama_french_betas_wide <- df_fama_french_betas %>%
        dcast.data.table(symbol ~ term, value.var = "factor_beta")
    
    df_stocks <- df_stocks %>%
        merge(df_fama_french_betas_wide, by = "symbol", all.x = TRUE, all.y = FALSE)
    
    # fama french second stage estimation
    
    flog.info(glue("    estimating fama french second stage for {end_date}..."))
    
    fit_xs_regression <- function(sd) {
        sd_annotated <- sd %>% copy()
        rownames(sd_annotated) <- sd$symbol
        regression_model = list(lm(
            formula = clean_log_return ~ market_factor_beta + size_factor_beta + momentum_factor_beta,
            data = sd_annotated
        ))
        return(regression_model)
    }
    
    df_xs_regressions <- df_stocks %>% .[, list(regression_model = fit_xs_regression(.SD)), by = date]

    df_fama_macbeth_augmented <- df_xs_regressions %>%
        .[, augment(regression_model[[1]]), by = date] %>%
        .[, list(
            regression_date = date, symbol = .rownames,
            clean_log_return,
            market_factor_beta, size_factor_beta, momentum_factor_beta,
            fitted = .fitted, fitted_se = .se.fit, residuals = .resid
        )] %>%
        setkey(symbol, regression_date)
        
    df_fama_macbeth_returns <- df_xs_regressions %>%
        .[, tidy(regression_model[[1]]), by = date] %>%
        .[term != "(Intercept)"] %>%
        .[, term := gsub("_factor_beta", "_factor_return", term)] %>%
        .[, factor_return := estimate] %>%
        .[, list(term, regression_date = date, factor_return)] %>%
        .[, cumulative_factor_return := factor_return %>% coalesce(0) %>% cumsum(), by = term] %>%
        setkey(term, regression_date)
    
    df_fama_macbeth_returns_wide <- df_fama_macbeth_returns %>%
        dcast.data.table(regression_date ~ term, value.var = "factor_return")    
    
    # tested ARMA, urned out not useful at all! back to iid
    
    fit_arima <- function(factor_return) {
        arima_model <- arima(factor_return, order = c(1, 0, 0))
        fitted <- arima_model %>% forecast(h = 21)
        # ...
    }
    
    df_fama_macbeth_return_estimates <- df_fama_macbeth_returns %>%
        .[
            j = list(
                factor_mean = 252 * nan_mean(factor_return),
                factor_volatility = sqrt(252) * nan_sd(factor_return),
                factor_sharpe = sqrt(252) * nan_mean(factor_return) / nan_sd(factor_return)
            ),
            keyby = term
        ] %>%
        .[j = `:=`(
            factor_mean_prior = c(0.04, 0.02, 0.02),
            factor_volatility_prior = c(0.16, 0.16, 0.16),
            factor_sharpe_prior = c(0.25, 0.125, 0.125)
        )]
    
    df_fama_macbeth_correlation_estimates <- df_fama_macbeth_returns_wide[, -1] %>%
        cor()
    
    # convert factor estimates into stock estimates
    
    flog.info(glue("    computing estimates for {end_date}..."))
    
    factor_beta_columns <- c("market_factor_beta", "momentum_factor_beta", "size_factor_beta")
    factor_return_columns <- c("market_factor_return", "momentum_factor_return", "size_factor_return")
    
    all_returns <- df_stocks[, clean_log_return] %>% as.matrix()
    returns <- df_stocks[date == max(date), clean_log_return] %>% as.matrix()
    all_factor_betas <- df_stocks[, (factor_beta_columns), with = FALSE] %>% as.matrix()
    factor_betas <- df_stocks[date == max(date), (factor_beta_columns), with = FALSE] %>% as.matrix()
    symbols <- df_stocks[date == max(date), symbol]
    
    factor_means <- df_fama_macbeth_return_estimates$factor_mean %>% as.matrix()
    factor_vols <- df_fama_macbeth_return_estimates$factor_volatility %>% diag()
    factor_correls <- df_fama_macbeth_correlation_estimates %>% as.matrix()
    factor_cov <- factor_vols %*% factor_correls %*% factor_vols
    
    expected_return_from_factors <- factor_betas %*% factor_means
    expected_variance_from_factors <- factor_betas %*% factor_cov %*% t(factor_betas)
    
    # tested GARCH, works for many stocks, better than iid, but only marginally
    # too computationally intensive, not worth the benefit
    
    fit_garch <- function(residuals) {
        garch_model <- ugarchspec(
            variance.model = list(model = 'sGARCH', garchOrder = c(1, 1)),
            mean.model = list(armaOrder = c(1, 0), include.mean = FALSE),
            distribution.model = 'norm'
        )
        estimated_vol <- ugarchfit(spec = garch_model, data = residuals) %>%
            ugarchforecast(n.ahead = horizon_lengths) %>%
            sigma() %>%
            tail(1) %>%
            as.numeric()
        estimated_var <- estimated_vol ^ 2
        return(estimated_var)
    }
    
    # garch here...
    df_fama_macbeth_augmented <- df_fama_macbeth_augmented %>%
        .[, expected_variance_from_idiosyncratic := 252 * nan_var(residuals), by = symbol]
    
    expected_variance_from_idiosyncratic <- df_fama_macbeth_augmented[regression_date == max(regression_date), expected_variance_from_idiosyncratic] %>% diag()
    expected_variance <- expected_variance_from_factors + expected_variance_from_idiosyncratic
    
    expected_factor_vol <- expected_variance_from_factors %>% diag() %>% sqrt()
    expected_idiosyncratic_vol <- expected_variance_from_idiosyncratic %>% diag() %>% sqrt()
    expected_vol <- expected_variance %>% diag() %>% sqrt()
    
    # black litterman shrinkage
    # priors == views (oops I switched the semantics)
    # sigma_est >> sigma_bl, thus not worth incorporating into expected vol (matrix inversions for no gain...)
    # embed relative weights of sigma and omega in tau directly, assume close to diagonal covariances and uncertainties
    
    modified_tau <- 0.99
    factor_means_prior <- df_fama_macbeth_return_estimates$factor_mean_prior %>% as.matrix()
    factor_vols_prior <- df_fama_macbeth_return_estimates$factor_volatility_prior %>% diag()
    expected_return_prior <- factor_betas %*% factor_means_prior
    expected_return_prior_uncertainty <- factor_betas %*% (factor_vols_prior %*% factor_vols_prior) %*% t(factor_betas)
    expected_return_bl <- modified_tau * expected_return_prior + (1 - modified_tau) * expected_return_from_factors
    expected_vol <- expected_vol
    
    df_estimates <- df_stocks %>%
        .[date == max(date)] %>%
        .[j = list(symbol)] %>%
        .[, estimated_start_date := start_date] %>%
        .[, estimated_end_date := end_date] %>%
        .[, estimated_return_factor_model := expected_return_from_factors] %>%
        .[, estimated_return_prior := expected_return_prior] %>%
        .[, estimated_mean := expected_return_bl] %>%
        .[, estimated_vol_factor_model := expected_vol] %>%
        .[, estimated_factor_vol_factor_model := expected_factor_vol] %>%
        .[, estimated_idiosyncratic_vol_factor_model := expected_idiosyncratic_vol] %>%
        .[, estimated_vol := expected_vol] %>%
        .[, estimated_sharpe := estimated_mean / estimated_vol]
        
    model <- list(
        estimates = df_estimates,
        estimated_return = data.table(symbol = symbols, expected_return = expected_return_bl %>% as.vector()),
        estimated_variance = expected_variance_from_factors %>% as.data.table() %>% setnames(symbols) %>% .[, symbol := symbols],
        ff_betas = df_fama_french_betas,
        ff_returns = df_fama_macbeth_returns,
        ff_augmented = df_fama_macbeth_augmented,
        ff_return_estimates = df_fama_macbeth_return_estimates,
        ff_correl_estimates = df_fama_macbeth_correlation_estimates %>% as.data.table() %>% .[, term := factor_return_columns]
    )
    
    return(model)
    
}

realized_simple <- function(df) {
    
    realize_mean <- function(r) nan_mean(r)
    realize_vol <- function(r) nan_sd(r)
    realize_sharpe <- function(r) realize_mean(r) / realize_vol(r)
    # realize_beta <- function(r, m) cov(r, m, use = "pairwise.complete.obs") / nan_var(m)
    
    df_realized <- df %>%
        .[
            j = list(
                realized_start_date = min(date),
                realized_end_date = max(date),
                realized_mean = 252 * realize_mean(clean_log_return),
                realized_vol = sqrt(252) * realize_vol(clean_log_return),
                realized_sharpe = sqrt(252) * realize_sharpe(clean_log_return)
                # realized_beta = realize_beta(clean_log_return, market_log_return)
            ),
            keyby = symbol
            ]        
    
    return(df_realized)            
    
}

combine_results <- function(all_models, result_type) {
    map(all_models, function(model) model %>% pluck(result_type)) %>%
        rbindlist(idcol = "date", use.names = TRUE, fill = TRUE) %>%
        .[, date := as.Date(date)]
}

estimate_signals <- function(df_clean) {
    
    df_data <- df_clean %>%
        copy() %>%
        setkey(symbol, date) %>%
        setindex(date)

    ls_estimations <- list()
    ls_realizations <- list()
    ls_weights <- list()
    
    for (current_date in as.list(rolling_dates)) {
        
        if (current_date %in% log_dates) flog.info(glue('running estimation on date {current_date}...'))
        
        estimation_date_start <- max(current_date - days(rolling_window_lengths), min_date)
        estimation_date_end <- current_date - days(1)
        if (current_date %in% log_dates) flog.info(glue('  estimation window from {estimation_date_start} to {estimation_date_end}...'))
        
        model_estimation <- df_data[date %between% c(estimation_date_start, estimation_date_end)] %>% estimation_factor_model
        ls_estimations[[as.character(current_date)]] <- model_estimation
        
        forecast_date_start <- current_date
        forecast_date_end <- min(current_date + days(horizon_lengths), max_date)
        if (current_date %in% log_dates) flog.info(glue('  realization window from {forecast_date_start} to {forecast_date_end}...'))
        
        df_realization <- df_data[date %between% c(forecast_date_start, forecast_date_end)] %>% realized_simple
        ls_realizations[[as.character(current_date)]] <- df_realization
        
    }
    
    # combine estimates
    df_estimated <- combine_results(ls_estimations, "estimates")
    df_estimated_return <- combine_results(ls_estimations, "estimated_return")
    df_estimated_variance <- combine_results(ls_estimations, "estimated_variance")
    df_ff_betas <- combine_results(ls_estimations, "ff_betas")
    df_ff_returns <- combine_results(ls_estimations, "ff_returns")
    df_ff_estimated_returns <- combine_results(ls_estimations, "ff_return_estimates")
    df_ff_estimated_correlations <- combine_results(ls_estimations, "ff_correl_estimates")
    
    # combine realizations
    df_realized <- rbindlist(ls_realizations, idcol = 'date') %>% .[, date := as.Date(date)]
    
    # store
    df_signals <- df_data %>%
        copy() %>%
        .[date %between% c(start_date, end_date)] %>%
        merge(df_estimated, by = c("symbol", "date"), all.x = TRUE, all.y = FALSE) %>%
        merge(df_realized, by = c("symbol", "date"), all.x = TRUE, all.y = FALSE)
    
    # return
    model <- list(
        df_signals = df_signals,
        df_ff_betas = df_ff_betas,
        df_ff_returns = df_ff_returns,
        df_ff_estimated_returns = df_ff_estimated_returns,
        df_ff_estimated_correlations = df_ff_estimated_correlations,
        df_estimated_return = df_estimated_return,
        df_estimated_variance = df_estimated_variance
    )
    
    return(model)   
}


# portfolio

construct_portfolio_equal_weight <- function(df_estimation, df_expected_variance_full) {
    df_estimation %>%
        .[, weight := 1 / .N] %>%
        .[j = list(symbol, weight)]
}

construct_portfolio_naive_risk_parity <- function(df_estimation, df_expected_variance_full) {
    df_estimation %>%
        copy() %>%
        .[, weight := (1 / estimated_vol)] %>%
        .[, weight := weight / sum(abs(weight), na.rm = TRUE)] %>%
        .[j = list(symbol, weight)]
}

construct_portfolio_dynamic_risk_parity <- function(df_estimation, df_expected_variance_full) {
    df_estimation %>%
        copy() %>%
        .[, weight := (1 / estimated_vol) * (estimated_sharpe %>% na.fill(0) %>% frank())] %>%
        .[, weight := weight / sum(abs(weight), na.rm = TRUE)] %>%
        .[j = list(symbol, weight)]
}

construct_portfolio_optimized_long_short <- function(df_estimation_full, df_expected_variance_full) {
    
    df_top <- df_estimation_full %>% .[!is.na(estimated_sharpe)] %>% .[order(estimated_sharpe)] %>% head(50)
    df_bot <- df_estimation_full %>% .[!is.na(estimated_sharpe)] %>% .[order(estimated_sharpe)] %>% tail(50)
    df_estimation <- rbindlist(list(df_top, df_bot), use.names = TRUE, fill = TRUE, idcol = FALSE)
    
    n <- nrow(df_estimation)
    used_symbols <- df_estimation$symbol
    
    df_mean <- df_estimation_full %>%
        .[used_symbols, estimated_mean, on = "symbol"]
    
    df_variance <- df_expected_variance_full %>%
        .[used_symbols, !(c("date", "symbol")), with = FALSE, on = "symbol"] %>%
        .[, (used_symbols), with = FALSE] 
    
    mu <- df_mean %>% as.matrix()
    Sigma <- df_variance %>% as.matrix()
    
    w <- Variable(n)
    ret <- t(mu) %*% w
    risk <- quad_form(w, Sigma)
    gross_notional <- CVXR::p_norm(w, 1)
    net_notional <- CVXR::sum_entries(w)
    
    objective <- ret - 1 * (0.5) * risk
    constraints <- list(
        net_notional == 1,
        gross_notional <= 1.30,
        w <= 0.10,
        w >= -0.10
    )

    prob <- Problem(Maximize(objective), constraints)
    result <- solve(prob)
    
    df_optimized_properties <- data.table(
        portfolio_return = result$getValue(ret),
        portfolio_volatility = result$getValue(sqrt(risk)),
        portfolio_gross_notional = result$getValue(gross_notional),
        portfolio_net_notional = result$getValue(net_notional)
    )
    
    normalize <- function(w) w / nan_sum(abs(w))
    
    df_optimized_weights <- data.table(
        symbol = df_estimation$symbol,
        weight = result$getValue(w) %>% as.vector()
    )
    
    model <- list(
        weights = df_optimized_weights,
        properties = df_optimized_properties
    )
    
    return(model$weights)
}

construct_portfolio <- function(df_signals, df_estimated_variance, construction_function) {
    
    df_signals_pc <- df_signals
    df_estimated_variance_pc <- df_estimated_variance
    
    ls_weights <- list()
    
    for (current_date in as.list(rolling_dates)) {
        
        weight_date <- current_date
        if (current_date %in% log_dates) flog.info(glue('portfolio construction date on {weight_date}...'))
        
        df_estimation <- df_signals_pc[date == current_date] %>% .[!is.na(estimated_sharpe)] 
        df_variance <- df_estimated_variance_pc[date == current_date]
        
        if (nrow(df_estimation) == 0) {
            df_weight <- NULL
            ls_weights[[as.character(current_date)]] <- df_weight
        } else {
            df_weight <- construction_function(df_estimation, df_variance)
            ls_weights[[as.character(current_date)]] <- df_weight
        }
    }
    
    # smooth weights
    df_all_weights <- rbindlist(ls_weights, idcol = 'date') %>%
        .[, date := as.Date(date)] %>%
        .[!is.na(weight)] %>%
        .[, ideal_weight := weight] %>%
        .[, weight := 0.5 * (ideal_weight + shift(ideal_weight)), by = symbol]
    
    df_constructed <- df_signals_pc %>%
        copy() %>%
        merge(df_all_weights, by = c("symbol", "date"), all.x = TRUE, all.y = FALSE) %>%
        .[, weight := weight %>% zoo::na.locf(na.rm = FALSE) %>% na.fill(0), by = symbol] %>%
        .[, lagged_weight := shift(weight), by = symbol] %>%
        .[, drifted_weight := shift(weight) * (1 + clean_log_return), by = symbol]
    
    # .[, quantity := weight / clean_adjclose] %>%
    # .[, drifted_quantity := shift(quantity), by = symbol] %>%
    # .[, drifted_weight := drifted_quantity * clean_adjclose / nan_sum(drifted_quantity * clean_adjclose), by = date]
    
    return(df_constructed)
}

construct_portfolio_variants <- function(df_signals, df_expected_variance, df_benchmark) {

    portfolio_variants <- list(
        '1. Equal Weight' = construct_portfolio_equal_weight,
        '2. Naive Risk Parity' = construct_portfolio_naive_risk_parity,
        '3. Dynamic Risk Parity' = construct_portfolio_dynamic_risk_parity,
        '4. Optimized Long Short' = construct_portfolio_optimized_long_short
    ) 
    
    df_constructed <- portfolio_variants %>%
        lapply(function(f) construct_portfolio(df_signals, df_expected_variance, f)) %>%
        rbindlist(idcol = "portfolio_method", use.names = TRUE, fill = TRUE)
    
    constructed_and_benchmark <- list(
        Project = df_constructed,
        Benchmark = df_benchmark
    )
    
    df_constructed <- constructed_and_benchmark %>%
        rbindlist(idcol = 'project_or_benchmark', use.names = TRUE, fill = TRUE)
    
    return(df_constructed)
}

# portfolio aggregation and evaluation

aggregate_portfolio <- function(df) {
    
    df_portf <- df %>%
        copy() %>%
        .[date %between% c(start_date, end_date)]
    
    scale <- df_portf %>%
        .[, list(portfolio_log_return = nan_sum(lagged_weight * log_return)), by = date] %>%
        .[, list(full_sample_vol = sqrt(252) * nan_sd(portfolio_log_return))] %>%
        .[, (0.15 / full_sample_vol)] 
        
    df_portf_scaled <- df_portf %>%
        .[, weight := scale * weight] %>%
        .[, lagged_weight := scale * lagged_weight] %>%
        .[, drifted_weight := scale * drifted_weight]
        
    df_portf_scaled %>%
        .[
            j = list(
                portfolio_gross_weight = nan_sum(abs(weight)),
                portfolio_net_weight = nan_sum(weight),
                portfolio_log_return = nan_sum(lagged_weight * log_return),
                portfolio_turnover = nan_sum(weight - lagged_weight),
                portfolio_absolute_turnover = ifelse(
                    all(lagged_weight == 0),
                    0,
                    nan_sum(abs(weight - drifted_weight))
                ) %>% as.double(),
                portfolio_pecentage_turnover = ifelse(
                    all(lagged_weight == 0),
                    0,
                    nan_sum(abs(weight - drifted_weight)) / nan_sum(abs(lagged_weight))
                ) %>% as.double()
            ),
            keyby = date
            ] %>%
        .[, portfolio_cost := (kappa * portfolio_absolute_turnover) * abs(1 + portfolio_log_return)] %>%
        .[, portfolio_net_log_return := portfolio_log_return - portfolio_cost] %>%
        .[, cumulative_portfolio_log_return := portfolio_log_return %>% nan_cumsum] %>%
        .[, cumulative_portfolio_net_log_return := portfolio_net_log_return %>% nan_cumsum] 
}

evaluate_portfolio <- function(df) {
    df %>%
        copy() %>%
        .[
            j = list(
                portfolio_mean_return = 252 * nan_mean(portfolio_log_return),
                portfolio_mean_cost = 252 * nan_mean(portfolio_cost),
                portfolio_post_cost_mean_return = 252 * nan_mean(portfolio_net_log_return),
                portfolio_cost_percentage = nan_mean(portfolio_cost) / nan_mean(portfolio_log_return),
                portfolio_volatility = sqrt(252) * nan_sd(portfolio_log_return),
                portfolio_sharpe_ratio = sqrt(252) * nan_mean(portfolio_net_log_return) / nan_sd(portfolio_net_log_return),
                portfolio_sortino_ratio = sqrt(252) * PerformanceAnalytics::SortinoRatio(portfolio_net_log_return),
                portfolio_max_drawdown = -1 * PerformanceAnalytics::maxDrawdown(portfolio_net_log_return, geometric = FALSE),
                portfolio_average_percentage_turnover = nan_mean(portfolio_pecentage_turnover)
            )
            ]
}


# utilities

select_sample <- function(df, column, n = 10) {
    df %>%
        .[get(column) %in% sample(get(column), n, replace = FALSE)]
}

select_top <- function(df, column, n = 10) {
    df_top <- df[order(get(column), decreasing = TRUE)] %>% head(n)
    return(df_top)
}

select_top_bottom <- function(df, column, n = 10) {
    df_top <- df[order(get(column))] %>% head(n)
    df_bottom <- df[order(get(column))] %>% tail(n)
    df_top_bottom <- rbindlist(list(df_top, df_bottom))
    return(df_top_bottom)
}

select_top_bottom_by_group <- function(df, column, by, n = 10) {
    df_top <- df[, .SD[order(get(column))] %>% head(n), by = by]
    df_bottom <- df[, .SD[order(get(column))] %>% tail(n), by = by]
    df_top_bottom <- rbindlist(list(df_top, df_bottom))
    return(df_top_bottom)
}

select_top_by_group <- function(df, column, by, n = 10) {
    df_top <- df[, .SD[order(get(column), decreasing = TRUE)] %>% head(n), by = by]
    return(df_top)
}
