\name{quercus_nf3}
\alias{quercus_nf3}
\title{Three-Component Maximum Likelihood Analysis of Quantitative Genetic Data}
\usage{
quercus_nf3(
  data,
  method = "REML",
  nchar = NULL,
  nfixed = 0L,
  feasibility = FALSE,
  constraints = NULL,
  start_values = NULL,
  model = "dominance",
  trait_cols = NULL,
  fixed_cols = NULL,
  workdir = NULL,
  exe = NULL,
  verbose = FALSE
)
}
\arguments{
\item{data}{A data frame with columns \code{id}, \code{father},
\code{mother}, optionally fixed-factor columns, and phenotype column(s).
Founders must have \code{father = mother = 0} and missing phenotypes
encoded as \code{NA}.}

\item{method}{Character; \code{"REML"} (default) or \code{"ML"}.}

\item{nchar}{Integer; number of traits to analyse.  If \code{NULL},
inferred automatically.}

\item{nfixed}{Integer; number of categorical fixed factors beyond the grand
mean (default \code{0}).}

\item{feasibility}{Logical; impose positive-definiteness constraints
(default \code{FALSE}).}

\item{constraints}{Integer vector of component indices to constrain to zero.
Components are ordered: additive, environmental, dominance/CE.  Within
each type, elements are indexed in upper-triangular order.}

\item{start_values}{Numeric vector of starting values for the variance
components.}

\item{model}{Character; \code{"dominance"} (default) or
\code{"common_environment"}.  This is a compile-time constant in the Pascal
source (\code{ceo}); it cannot be changed without recompiling.}

\item{trait_cols}{Character vector (or integer indices) of phenotype columns
in \code{data}.}

\item{fixed_cols}{Character vector (or integer indices) of fixed-factor
columns in \code{data}.}

\item{workdir}{Working directory for the program.  A temporary directory is
used by default.}

\item{exe}{Path to the \code{nf3} executable.  Autodetected if \code{NULL}.}

\item{verbose}{Logical; print program standard output (default
\code{FALSE}).}
}
\value{
A list of class \code{"quercus_result"} with elements:
\describe{
  \item{\code{program}}{\code{"nf3"}}
  \item{\code{method}}{\code{"ML"} or \code{"REML"}}
  \item{\code{converged}}{Logical}
  \item{\code{constrained}}{Logical}
  \item{\code{log_likelihood}}{Numeric log-likelihood}
  \item{\code{iterations}}{Integer iteration count}
  \item{\code{means}}{Numeric vector of trait grand means}
  \item{\code{fixed_effects}}{Numeric vector of fixed-effect estimates}
  \item{\code{components}}{Named list of variance-covariance matrices}
  \item{\code{varcov}}{Large-sample variance-covariance matrix of estimates}
  \item{\code{raw_output}}{Character vector of program output}
}
}
\description{
Calls the \code{nf3} Pascal program to estimate additive, dominance (or
common-environment), and environmental variance-covariance components by ML
or REML from a two-generation pedigree.
}
\details{
\code{nf3} is computationally efficient for designs with at most three
variance components.  For diallel data with up to six components use
\code{\link{quercus_nf6}}.

The variance components are ordered: additive, environmental, dominance (or
common environment).  Within each component type, elements of the
variance-covariance matrix are indexed in upper-triangular order.
}
\examples{
\dontrun{
compile_quercus()
demo_file <- system.file("extdata", "sibships.demo1", package = "quercus")
dat <- read_sibships(demo_file)
result <- quercus_nf3(dat)
print(result)
result$components$Additive
}
}
\references{
Shaw, R. G. (1987). Maximum-likelihood approaches applied to quantitative
genetics of natural populations. \emph{Evolution}, 41(4), 812--826.

Shaw, R. G. and Geyer, C. J. (1997). Estimation and testing in constrained
covariance component models. \emph{Biometrika}, 84(1), 95--102.
}
\seealso{
\code{\link{quercus_nf6}}, \code{\link{quercus_pcrf1}},
\code{\link{quercus_fend}}, \code{\link{compile_quercus}},
\code{\link{write_sibships}}, \code{\link{read_sibships}}
}
