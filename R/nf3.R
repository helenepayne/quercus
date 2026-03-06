#' Three-component maximum likelihood analysis of quantitative genetic data
#'
#' Calls the \code{nf3} Pascal program to estimate additive, dominance (or
#' common-environment), and environmental variance-covariance components by
#' ML or REML from a two-generation pedigree.
#'
#' \code{nf3} is computationally efficient for designs with at most three
#' variance components (parent-offspring, nested sib, half-sib, etc.).  For
#' diallel data with up to six components use \code{\link{quercus_nf6}}.
#'
#' Before calling this function, compile the Pascal programs with
#' \code{\link{compile_quercus}}.
#'
#' @param data A data frame with columns \code{id}, \code{father},
#'   \code{mother}, optionally fixed-factor columns, and phenotype column(s).
#'   Founders (parents with unknown parentage) must have
#'   \code{father = mother = 0} and missing phenotypes encoded as \code{NA}.
#' @param method Character; \code{"REML"} (default) or \code{"ML"}.
#' @param nchar Integer; number of traits to analyse.  If \code{NULL},
#'   inferred from \code{trait_cols} or the data.
#' @param nfixed Integer; number of categorical fixed factors beyond the grand
#'   mean (default \code{0}).
#' @param feasibility Logical; impose positive-definiteness constraints on the
#'   variance-covariance matrices (default \code{FALSE}).
#' @param constraints Integer vector of component indices to constrain to zero
#'   (see the Quercus documentation for index ordering).
#' @param start_values Numeric vector of starting values for the variance
#'   components.
#' @param model Character; \code{"dominance"} (default) or
#'   \code{"common_environment"}.  Controls the \code{ceo} constant in the
#'   Pascal source; note this cannot be changed at run time without
#'   recompiling — the option is recorded in the result for documentation
#'   purposes.
#' @param trait_cols Character vector (or integer indices) of phenotype
#'   column names in \code{data}.
#' @param fixed_cols Character vector (or integer indices) of fixed-factor
#'   column names in \code{data}.
#' @param workdir Path to a directory used as the working directory for the
#'   program.  A temporary directory is used by default.
#' @param exe Path to the \code{nf3} executable.  Autodetected via
#'   \code{\link{find_exe}} if \code{NULL}.
#' @param verbose Logical; print the program's standard output (default
#'   \code{FALSE}).
#'
#' @return A list of class \code{"quercus_result"} with elements:
#' \describe{
#'   \item{\code{program}}{\code{"nf3"}}
#'   \item{\code{method}}{\code{"ML"} or \code{"REML"}}
#'   \item{\code{converged}}{Logical}
#'   \item{\code{constrained}}{Logical}
#'   \item{\code{log_likelihood}}{Numeric}
#'   \item{\code{iterations}}{Integer}
#'   \item{\code{means}}{Numeric vector of trait grand means}
#'   \item{\code{fixed_effects}}{Numeric vector of fixed-effect estimates}
#'   \item{\code{components}}{Named list of variance-covariance matrices
#'     (\code{Additive}, \code{Environmental}, \code{Dominance} or
#'     \code{Common Environment})}
#'   \item{\code{varcov}}{Large-sample variance-covariance matrix of estimates}
#'   \item{\code{raw_output}}{Character vector of all program output lines}
#' }
#'
#' @references
#' Shaw, R. G. (1987). Maximum-likelihood approaches applied to quantitative
#' genetics of natural populations. \emph{Evolution}, 41(4), 812--826.
#'
#' Shaw, R. G. and Geyer, C. J. (1997). Estimation and testing in constrained
#' covariance component models. \emph{Biometrika}, 84(1), 95--102.
#'
#' @examples
#' \dontrun{
#' compile_quercus()
#' demo_file <- system.file("extdata", "sibships.demo1", package = "quercus")
#' dat <- read_sibships(demo_file)
#' result <- quercus_nf3(dat)
#' print(result)
#' }
#'
#' @export
quercus_nf3 <- function(data,
                         method       = "REML",
                         nchar        = NULL,
                         nfixed       = 0L,
                         feasibility  = FALSE,
                         constraints  = NULL,
                         start_values = NULL,
                         model        = "dominance",
                         trait_cols   = NULL,
                         fixed_cols   = NULL,
                         workdir      = NULL,
                         exe          = NULL,
                         verbose      = FALSE) {

  exe     <- exe %||% find_exe("nf3")
  method_int <- switch(toupper(method), "REML" = 2L, "ML" = 1L,
                       stop("'method' must be 'ML' or 'REML'."))

  workdir <- workdir %||% tempfile("quercus_nf3_")
  if (!dir.exists(workdir)) dir.create(workdir, recursive = TRUE)

  sibships_file <- file.path(workdir, "sibships")
  # nf3 writes its output as 'analysis' (lowercase) per FPC-compatible build
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

  # Accept either case for portability (macOS is case-insensitive by default)
  if (!file.exists(analysis_file)) {
    analysis_file <- file.path(workdir, "Analysis")
  }
  if (!file.exists(analysis_file)) {
    stop("nf3 did not produce an analysis output file.\nProgram output:\n",
         paste(out, collapse = "\n"))
  }

  nc <- nchar %||% infer_nchar(data, trait_cols, fixed_cols, nfixed)
  res <- parse_analysis(analysis_file, nchar = nc)
  res$program <- "nf3"
  res$model   <- model
  class(res)  <- "quercus_result"
  res
}


#' @keywords internal
`%||%` <- function(x, y) if (is.null(x)) y else x


#' Run a Quercus executable in a given working directory
#' @keywords internal
run_quercus <- function(exe, workdir, verbose = FALSE) {
  old_wd <- setwd(workdir)
  on.exit(setwd(old_wd), add = TRUE)

  out <- system2(exe, stdout = TRUE, stderr = TRUE)

  if (isTRUE(verbose)) {
    message(paste(out, collapse = "\n"))
  }
  invisible(out)
}


#' Infer the number of traits from the data frame
#' @keywords internal
infer_nchar <- function(data, trait_cols, fixed_cols, nfixed) {
  if (!is.null(trait_cols)) return(length(trait_cols))
  remaining <- setdiff(names(data), c("id", "father", "mother"))
  if (is.null(fixed_cols) && nfixed > 0L) {
    fixed_cols <- remaining[seq_len(nfixed)]
  }
  length(setdiff(remaining, fixed_cols))
}


#' @export
print.quercus_result <- function(x, ...) {
  cat("Quercus", x$program, "result\n")
  cat("Method:", x$method, "\n")
  cat("Converged:", x$converged,
      if (isTRUE(x$constrained)) "(feasibility constraints applied)" else "",
      "\n")
  if (!is.na(x$log_likelihood)) {
    cat("Log-likelihood:", x$log_likelihood, "\n")
  }
  if (!is.null(x$iterations) && !is.na(x$iterations)) {
    cat("Iterations:", x$iterations, "\n")
  }
  if (length(x$means) > 0L) {
    cat("Trait means:", paste(round(x$means, 6L), collapse = "  "), "\n")
  }
  if (length(x$components) > 0L) {
    cat("Components estimated:", paste(names(x$components), collapse = ", "), "\n")
    for (nm in names(x$components)) {
      cat("\n", nm, ":\n", sep = "")
      print(round(x$components[[nm]], 6L))
    }
  }
  invisible(x)
}
