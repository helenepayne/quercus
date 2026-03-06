#' Compare genetic variance-covariance matrices between two populations
#'
#' Calls the \code{pcrf1} Pascal program, which extends \code{nf3} to jointly
#' estimate three variance components for each of two genetically unrelated
#' populations and optionally tests whether the additive (G) matrices are equal.
#'
#' The input data frame must contain individuals from both populations.  The
#' first fixed factor must be an integer population identifier (1 or 2).
#'
#' Before calling this function, compile the Pascal programs with
#' \code{\link{compile_quercus}}.
#'
#' @inheritParams quercus_nf3
#' @param g_constraints Integer vector of additive component indices to
#'   constrain equal across the two populations (see the Quercus documentation
#'   for the index ordering).  An empty or \code{NULL} value estimates the G
#'   matrices separately.
#'
#' @return A list of class \code{"quercus_result"} with the same elements as
#'   \code{\link{quercus_nf3}} plus:
#' \describe{
#'   \item{\code{g_constraints}}{Integer vector of constrained G-matrix
#'     indices supplied by the user.}
#' }
#'
#' @references
#' Shaw, R. G. (1991). The comparison of quantitative genetic parameters
#' between populations. \emph{Evolution}, 45(1), 143--151.
#'
#' Shaw, R. G. and Billington, H. L. (1991). Comparison of variance components
#' between two populations of \emph{Holcus lanatus}. \emph{Evolution},
#' 45(5), 1287--1298.
#'
#' @examples
#' \dontrun{
#' compile_quercus()
#' demo_file <- system.file("extdata", "pcdata.demo1", package = "quercus")
#' dat <- read_sibships(demo_file, nfixed = 2L)
#' # Estimate G matrices separately for both populations
#' res_unconst <- quercus_pcrf1(dat, nfixed = 2L)
#' # Constrain the full G matrix to be equal
#' res_const   <- quercus_pcrf1(dat, nfixed = 2L, g_constraints = 1:3)
#' }
#'
#' @export
quercus_pcrf1 <- function(data,
                            method        = "REML",
                            nchar         = NULL,
                            nfixed        = 1L,
                            feasibility   = FALSE,
                            constraints   = NULL,
                            g_constraints = NULL,
                            start_values  = NULL,
                            trait_cols    = NULL,
                            fixed_cols    = NULL,
                            workdir       = NULL,
                            exe           = NULL,
                            verbose       = FALSE) {

  exe        <- exe %||% find_exe("pcrf1")
  method_int <- switch(toupper(method), "REML" = 2L, "ML" = 1L,
                       stop("'method' must be 'ML' or 'REML'."))

  if (as.integer(nfixed) < 1L) {
    stop("'nfixed' must be >= 1 for pcrf1 (the first fixed factor must be the population ID).")
  }

  workdir <- workdir %||% tempfile("quercus_pcrf1_")
  if (!dir.exists(workdir)) dir.create(workdir, recursive = TRUE)

  pcdata_file <- file.path(workdir, "pcdata")
  pcout_file  <- file.path(workdir, "pcout")

  write_pcdata(
    data          = data,
    file          = pcdata_file,
    method        = method_int,
    nchar         = nchar,
    nfixed        = nfixed,
    feasibility   = feasibility,
    start_values  = start_values,
    constraints   = constraints,
    g_constraints = g_constraints,
    trait_cols    = trait_cols,
    fixed_cols    = fixed_cols
  )

  out <- run_quercus(exe, workdir, verbose)

  # pcrf1 names its output file "pcout" or "pcout.const" / "pcout.unconst"
  result_file <- pcout_file
  if (!file.exists(result_file)) {
    cands <- c(file.path(workdir, "pcout.const"),
               file.path(workdir, "pcout.unconst"),
               file.path(workdir, "Analysis"))
    result_file <- cands[file.exists(cands)][1L]
  }

  if (is.na(result_file) || !file.exists(result_file)) {
    stop("pcrf1 did not produce an output file.\nProgram output:\n",
         paste(out, collapse = "\n"))
  }

  nc  <- nchar %||% infer_nchar(data, trait_cols, fixed_cols, nfixed)
  res <- parse_pcout(result_file, nchar = nc)
  res$program       <- "pcrf1"
  res$g_constraints <- g_constraints
  class(res)        <- "quercus_result"
  res
}
