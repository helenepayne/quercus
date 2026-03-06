#' quercus: Maximum Likelihood Analysis of Quantitative Genetic Data
#'
#' The quercus package provides an R interface to the Quercus programs
#' developed by Ruth G. Shaw and Frank H. Shaw for maximum likelihood (ML)
#' and restricted maximum likelihood (REML) estimation of genetic and
#' environmental variances and covariances from two-generation pedigree data.
#'
#' @section Programs:
#' \describe{
#'   \item{\code{\link{quercus_nf3}}}{Three-component analysis (additive,
#'     dominance or common-environment, environmental).  Suitable for
#'     parent-offspring, nested sib, and half-sib designs.}
#'   \item{\code{\link{quercus_nf6}}}{Six-component analysis from diallel
#'     crosses with reciprocals (additive, dominance, environmental, maternal,
#'     paternal, nuclear-by-extranuclear interaction).}
#'   \item{\code{\link{quercus_pcrf1}}}{Comparison of genetic
#'     variance-covariance (G) matrices between two unrelated populations,
#'     with optional constraints for equality.}
#'   \item{\code{\link{quercus_fend}}}{Utility to determine minimum
#'     compile-time array constants for a given dataset.}
#' }
#'
#' @section Setup:
#' The analysis functions call compiled Pascal executables.  Before first use
#' install the Free Pascal Compiler (\url{https://www.freepascal.org/}) and
#' run:
#' \preformatted{
#' library(quercus)
#' compile_quercus()
#' }
#' Compiled binaries are cached in
#' \code{tools::R_user_dir("quercus", "cache")} and found automatically on
#' subsequent calls.
#'
#' @section Input data:
#' All analysis functions accept a data frame with columns \code{id},
#' \code{father}, \code{mother} (integer IDs; founders have 0 for both
#' parents), optionally fixed-factor columns, and one or more phenotype
#' columns.  Missing phenotypes should be \code{NA}.  Use
#' \code{\link{read_sibships}} to read existing Quercus-format files, or
#' build the data frame from any R source and pass it directly.
#'
#' @section Demo data:
#' Example datasets are installed with the package:
#' \preformatted{
#' system.file("extdata", "sibships.demo1", package = "quercus")
#' system.file("extdata", "sibships.demo2", package = "quercus")
#' system.file("extdata", "pcdata.demo1",   package = "quercus")
#' }
#'
#' @references
#' Shaw, R. G. (1987). Maximum-likelihood approaches applied to quantitative
#' genetics of natural populations. \emph{Evolution}, 41(4), 812--826.
#'
#' Shaw, R. G. and Geyer, C. J. (1997). Estimation and testing in constrained
#' covariance component models. \emph{Biometrika}, 84(1), 95--102.
#'
#' Cockerham, C. C. and Weir, B. S. (1977). Quadratic analyses of reciprocal
#' crosses. \emph{Biometrics}, 33(1), 187--203.
#'
#' @docType package
#' @name quercus-package
"_PACKAGE"
