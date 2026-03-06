#' Six-component maximum likelihood analysis of diallel data
#'
#' Calls the \code{nf6} Pascal program to estimate up to six variance-
#' covariance components (additive, dominance, environmental, maternal,
#' paternal, nuclear-by-extranuclear interaction) from a diallel cross with
#' reciprocals.
#'
#' Components inestimable from the design must be constrained to zero via
#' the \code{constraints} argument.  For designs with three or fewer
#' components (e.g. nested sib, parent-offspring) the more efficient
#' \code{\link{quercus_nf3}} is recommended.
#'
#' Before calling this function, compile the Pascal programs with
#' \code{\link{compile_quercus}}.
#'
#' @inheritParams quercus_nf3
#' @param ifound Integer; \code{0} (default) treats founders as non-inbred;
#'   \code{1} treats them as fully inbred.  Note: this is a compile-time
#'   constant in the Pascal source — the argument is recorded for
#'   documentation only and does not affect the binary unless recompiled.
#'
#' @return A list of class \code{"quercus_result"} (see
#'   \code{\link{quercus_nf3}} for element descriptions).  The
#'   \code{components} element may contain up to six named matrices:
#'   \code{Additive}, \code{Dominance}, \code{Environmental},
#'   \code{Maternal}, \code{Paternal}, and \code{Nuclear}.
#'
#' @references
#' Cockerham, C. C. and Weir, B. S. (1977). Quadratic analyses of reciprocal
#' crosses. \emph{Biometrics}, 33(1), 187--203.
#'
#' Shaw, R. G. (1987). Maximum-likelihood approaches applied to quantitative
#' genetics of natural populations. \emph{Evolution}, 41(4), 812--826.
#'
#' @examples
#' \dontrun{
#' compile_quercus()
#' demo_file <- system.file("extdata", "sibships.demo1", package = "quercus")
#' dat <- read_sibships(demo_file)
#' # Full diallel: estimate all 6 components
#' result <- quercus_nf6(dat)
#' print(result)
#' }
#'
#' @export
quercus_nf6 <- function(data,
                         method       = "REML",
                         nchar        = NULL,
                         nfixed       = 0L,
                         feasibility  = FALSE,
                         constraints  = NULL,
                         start_values = NULL,
                         ifound       = 0L,
                         trait_cols   = NULL,
                         fixed_cols   = NULL,
                         workdir      = NULL,
                         exe          = NULL,
                         verbose      = FALSE) {

  exe        <- exe %||% find_exe("nf6")
  method_int <- switch(toupper(method), "REML" = 2L, "ML" = 1L,
                       stop("'method' must be 'ML' or 'REML'."))

  workdir <- workdir %||% tempfile("quercus_nf6_")
  if (!dir.exists(workdir)) dir.create(workdir, recursive = TRUE)

  sibships_file <- file.path(workdir, "sibships")
  analysis_file <- file.path(workdir, "analysis")

  write_sibships(
    data         = data,
    file         = sibships_file,
    method       = method_int,
    nchar        = nchar,
    nfixed       = nfixed,
    feasibility  = feasibility,
    start_values = start_values,
    constraints  = constraints,
    trait_cols   = trait_cols,
    fixed_cols   = fixed_cols
  )

  out <- run_quercus(exe, workdir, verbose)

  if (!file.exists(analysis_file)) {
    analysis_file <- file.path(workdir, "Analysis")
  }
  if (!file.exists(analysis_file)) {
    stop("nf6 did not produce an analysis output file.\nProgram output:\n",
         paste(out, collapse = "\n"))
  }

  nc  <- nchar %||% infer_nchar(data, trait_cols, fixed_cols, nfixed)
  res <- parse_analysis(analysis_file, nchar = nc)
  res$program <- "nf6"
  res$ifound  <- as.integer(ifound)
  class(res)  <- "quercus_result"
  res
}
