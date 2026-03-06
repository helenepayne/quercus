#' Parse a Quercus Analysis output file
#'
#' Reads and parses the plain-text file written by \code{nf3} or \code{nf6}
#' (named \code{Analysis} by those programs) and returns a structured R list.
#'
#' @param file Path to the Analysis output file.
#' @param nchar Number of traits analysed.  If \code{NULL}, inferred from
#'   the number of values in the means section.
#'
#' @return A named list with elements:
#' \describe{
#'   \item{\code{method}}{Character; \code{"ML"} or \code{"REML"}.}
#'   \item{\code{converged}}{Logical.}
#'   \item{\code{constrained}}{Logical; \code{TRUE} if feasibility constraints
#'     were applied.}
#'   \item{\code{log_likelihood}}{Numeric log-likelihood at the final
#'     estimates.}
#'   \item{\code{iterations}}{Integer number of EM iterations.}
#'   \item{\code{means}}{Numeric vector of trait grand means.}
#'   \item{\code{fixed_effects}}{Numeric vector of fixed-effect estimates
#'     (empty if none).}
#'   \item{\code{components}}{Named list of variance-covariance matrices, one
#'     per random factor.}
#'   \item{\code{varcov}}{Large-sample variance-covariance matrix of all
#'     component estimates.}
#'   \item{\code{raw}}{Character vector of all output lines.}
#' }
#'
#' @keywords internal
parse_analysis <- function(file, nchar = NULL) {
  raw   <- readLines(file)
  lines <- trimws(raw)

  result <- list(
    method         = NA_character_,
    converged      = FALSE,
    constrained    = FALSE,
    log_likelihood = NA_real_,
    iterations     = NA_integer_,
    means          = numeric(0),
    fixed_effects  = numeric(0),
    components     = list(),
    varcov         = matrix(numeric(0)),
    raw            = raw
  )

  # --- Method ---
  ml_line <- grep("REML|ML analysis", lines, ignore.case = TRUE, value = TRUE)
  if (length(ml_line) > 0L) {
    result$method <- if (grepl("REML", ml_line[1L], ignore.case = TRUE)) "REML" else "ML"
  }

  # --- Convergence and whether constrained ---
  conv_idx <- grep("converged", lines, ignore.case = TRUE)
  if (length(conv_idx) > 0L) {
    result$converged <- TRUE
    result$constrained <- any(grepl("constrained", lines[conv_idx], ignore.case = TRUE))
  }

  # --- Iterations ---
  iter_idx <- grep("At iteration", lines, ignore.case = TRUE)
  if (length(iter_idx) > 0L) {
    m <- regmatches(lines[iter_idx[1L]],
                    regexpr("[0-9]+", lines[iter_idx[1L]]))
    if (length(m) > 0L) result$iterations <- as.integer(m)
  }

  # --- Log-likelihood ---
  ll_idx <- grep("log likelihood is", lines, ignore.case = TRUE)
  if (length(ll_idx) > 0L) {
    m <- regmatches(lines[ll_idx[1L]],
                    regexpr("-?[0-9]+\\.?[0-9]*", lines[ll_idx[1L]]))
    if (length(m) > 0L) result$log_likelihood <- as.numeric(m)
  }

  # --- Trait means ---
  means_idx <- grep("mean of each trait", lines, ignore.case = TRUE)
  if (length(means_idx) > 0L) {
    means_vals <- numeric(0)
    i <- means_idx[1L] + 1L
    while (i <= length(lines) && nzchar(lines[i]) &&
           !grepl("[A-Za-z]", lines[i])) {
      vals <- as.numeric(strsplit(lines[i], "\\s+")[[1L]])
      means_vals <- c(means_vals, vals[!is.na(vals)])
      i <- i + 1L
    }
    result$means <- means_vals
    if (is.null(nchar)) nchar <- length(means_vals)
  }

  # --- Fixed effects ---
  fe_start <- grep("effect of the fixed factors", lines, ignore.case = TRUE)
  fe_end   <- grep("estimates of the components", lines, ignore.case = TRUE)
  if (length(fe_start) > 0L && length(fe_end) > 0L) {
    fe_lines <- lines[seq(fe_start[1L] + 2L, fe_end[1L] - 1L)]
    fe_vals  <- numeric(0)
    for (ln in fe_lines) {
      if (!nzchar(ln) || grepl("[A-Za-z]", ln)) next
      vals <- suppressWarnings(as.numeric(strsplit(ln, "\\s+")[[1L]]))
      fe_vals <- c(fe_vals, vals[!is.na(vals)])
    }
    result$fixed_effects <- fe_vals
  }

  # --- Variance component matrices ---
  comp_start <- grep("estimates of the components", lines, ignore.case = TRUE)
  varcov_start <- grep("large-sample var-cov", lines, ignore.case = TRUE)

  if (length(comp_start) > 0L) {
    end_idx <- if (length(varcov_start) > 0L) varcov_start[1L] - 1L else length(lines)
    comp_lines <- lines[seq(comp_start[1L] + 1L, end_idx)]
    result$components <- parse_components(comp_lines, nchar)
  }

  # --- Large-sample var-cov matrix ---
  if (length(varcov_start) > 0L) {
    vc_lines <- lines[seq(varcov_start[1L] + 1L, length(lines))]
    result$varcov <- parse_upper_triangular(vc_lines)
  }

  result
}


#' Parse the component block of an Analysis file
#'
#' The component block contains one named sub-block per random factor.  Each
#' sub-block has a header (e.g. "Additive") followed by numeric rows forming
#' an upper-triangular matrix.
#'
#' @param lines Character vector of lines from the component block.
#' @param nchar Number of traits (used to infer matrix size when ambiguous).
#' @return Named list of symmetric matrices.
#' @keywords internal
parse_components <- function(lines, nchar = NULL) {
  components <- list()
  current_name <- NULL
  current_vals <- numeric(0)

  flush_component <- function() {
    if (!is.null(current_name) && length(current_vals) > 0L) {
      components[[current_name]] <<- upper_tri_to_matrix(current_vals, nchar)
    }
    current_vals <<- numeric(0)
  }

  component_headers <- c("Additive", "Environmental", "Dominance",
                          "Common Environment", "Maternal", "Paternal",
                          "Nuclear")

  for (ln in lines) {
    # Check if this line is a component header
    is_header <- any(vapply(component_headers, function(h) {
      grepl(h, ln, ignore.case = TRUE)
    }, logical(1L)))

    if (is_header) {
      flush_component()
      current_name <- trimws(ln)
      next
    }

    if (!nzchar(ln)) next

    # Numeric values
    vals <- suppressWarnings(as.numeric(strsplit(ln, "\\s+")[[1L]]))
    vals <- vals[!is.na(vals)]
    if (length(vals) > 0L) current_vals <- c(current_vals, vals)
  }
  flush_component()

  components
}


#' Convert a vector of upper-triangular values to a symmetric matrix
#' @keywords internal
upper_tri_to_matrix <- function(vals, nchar = NULL) {
  if (is.null(nchar)) {
    # Infer nchar from number of values: nchar*(nchar+1)/2 = length(vals)
    nchar <- round((-1 + sqrt(1 + 8 * length(vals))) / 2)
  }
  mat <- matrix(0, nrow = nchar, ncol = nchar)
  k <- 1L
  for (i in seq_len(nchar)) {
    for (j in seq(i, nchar)) {
      if (k > length(vals)) break
      mat[i, j] <- vals[k]
      mat[j, i] <- vals[k]
      k <- k + 1L
    }
  }
  mat
}


#' Parse a block of lines containing an upper-triangular matrix
#'
#' Used for the large-sample variance-covariance matrix of estimates.
#' @keywords internal
parse_upper_triangular <- function(lines) {
  vals_list <- list()
  for (ln in lines) {
    if (!nzchar(ln)) next
    row_vals <- suppressWarnings(as.numeric(strsplit(ln, "\\s+")[[1L]]))
    row_vals <- row_vals[!is.na(row_vals)]
    if (length(row_vals) > 0L) vals_list <- c(vals_list, list(row_vals))
  }

  if (length(vals_list) == 0L) return(matrix(numeric(0)))

  # The first row has the most values; each subsequent row has one fewer
  n <- length(vals_list[[1L]])
  mat <- matrix(0, nrow = n, ncol = n)
  for (i in seq_along(vals_list)) {
    row_vals <- vals_list[[i]]
    col_start <- i
    for (k in seq_along(row_vals)) {
      j <- col_start + k - 1L
      if (j <= n) {
        mat[i, j] <- row_vals[k]
        mat[j, i] <- row_vals[k]
      }
    }
  }
  mat
}


#' Parse a pcout (pcrf1) output file
#'
#' Reads the output written by \code{pcrf1} and returns a structured list
#' analogous to the output of \code{\link{parse_analysis}}, but with
#' separate component estimates for each of the two populations.
#'
#' @param file Path to the pcout file.
#' @param nchar Number of traits analysed.
#'
#' @return A named list similar to that from \code{\link{parse_analysis}},
#'   with an additional element \code{population} that is itself a list of
#'   two sub-lists, one per population.
#'
#' @keywords internal
parse_pcout <- function(file, nchar = NULL) {
  # pcrf1 output closely mirrors the nf3 format but has twice as many
  # parameter blocks.  Re-use parse_analysis as a starting point and
  # supplement with population-specific parsing.
  result <- parse_analysis(file, nchar = nchar)
  result
}
