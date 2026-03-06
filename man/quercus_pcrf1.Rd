\name{quercus_pcrf1}
\alias{quercus_pcrf1}
\title{Compare Genetic Variance-Covariance Matrices Between Two Populations}
\usage{
quercus_pcrf1(
  data,
  method = "REML",
  nchar = NULL,
  nfixed = 1L,
  feasibility = FALSE,
  constraints = NULL,
  g_constraints = NULL,
  start_values = NULL,
  trait_cols = NULL,
  fixed_cols = NULL,
  workdir = NULL,
  exe = NULL,
  verbose = FALSE
)
}
\arguments{
\item{data}{A data frame with individuals from both populations.  Must
contain \code{id}, \code{father}, \code{mother}, a population-ID column
(integer 1 or 2) as the first fixed factor, optionally more fixed factors,
and phenotype columns.}

\item{method}{Character; \code{"REML"} (default) or \code{"ML"}.}

\item{nchar}{Integer; number of traits.}

\item{nfixed}{Integer; number of fixed factors including the population
identifier (must be \eqn{\ge 1}).}

\item{feasibility}{Logical; impose positive-definiteness constraints.}

\item{constraints}{Integer vector of component indices to constrain to zero
in both populations.}

\item{g_constraints}{Integer vector of additive (G matrix) component
indices to constrain equal across populations.  \code{NULL} estimates the
G matrices separately.}

\item{start_values}{Numeric vector of starting values.}

\item{trait_cols}{Phenotype column names or indices.}

\item{fixed_cols}{Fixed-factor column names or indices.}

\item{workdir}{Working directory.  A temporary directory by default.}

\item{exe}{Path to the \code{pcrf1} executable.}

\item{verbose}{Print program output.}
}
\value{
A list of class \code{"quercus_result"} with the same elements as
\code{\link{quercus_nf3}} plus \code{g_constraints} (the integer vector
supplied by the user).
}
\description{
Calls the \code{pcrf1} Pascal program to jointly estimate three variance
components for each of two genetically unrelated populations, with optional
constraints for equality of the additive (G) matrix.
}
\examples{
\dontrun{
compile_quercus()
demo_file <- system.file("extdata", "pcdata.demo1", package = "quercus")
dat <- read_sibships(demo_file, nfixed = 2L)
# Estimate G separately for both populations
res_unconst <- quercus_pcrf1(dat, nfixed = 2L)
# Constrain full G to be equal
res_const   <- quercus_pcrf1(dat, nfixed = 2L, g_constraints = 1:3)
}
}
\references{
Shaw, R. G. (1991). The comparison of quantitative genetic parameters
between populations. \emph{Evolution}, 45(1), 143--151.
}
\seealso{
\code{\link{quercus_nf3}}, \code{\link{write_pcdata}},
\code{\link{compile_quercus}}
}
