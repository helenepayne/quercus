\name{quercus_nf6}
\alias{quercus_nf6}
\title{Six-Component Maximum Likelihood Analysis of Diallel Data}
\usage{
quercus_nf6(
  data,
  method = "REML",
  nchar = NULL,
  nfixed = 0L,
  feasibility = FALSE,
  constraints = NULL,
  start_values = NULL,
  ifound = 0L,
  trait_cols = NULL,
  fixed_cols = NULL,
  workdir = NULL,
  exe = NULL,
  verbose = FALSE
)
}
\arguments{
\item{data}{A data frame with pedigree and phenotype data.  See
\code{\link{quercus_nf3}} for column requirements.}

\item{method}{Character; \code{"REML"} (default) or \code{"ML"}.}

\item{nchar}{Integer; number of traits.}

\item{nfixed}{Integer; number of categorical fixed factors beyond the grand
mean.}

\item{feasibility}{Logical; impose positive-definiteness constraints.}

\item{constraints}{Integer vector of component indices to constrain to zero.
Components are ordered: additive, dominance, environmental, maternal,
paternal, nuclear-by-extranuclear interaction.}

\item{start_values}{Numeric vector of starting values.}

\item{ifound}{Integer; \code{0} (non-inbred founders, default) or \code{1}
(fully inbred founders).  This is a compile-time constant; the argument is
recorded for documentation only.}

\item{trait_cols}{Phenotype column names or indices.}

\item{fixed_cols}{Fixed-factor column names or indices.}

\item{workdir}{Working directory.  A temporary directory by default.}

\item{exe}{Path to the \code{nf6} executable.}

\item{verbose}{Print program output.}
}
\value{
A list of class \code{"quercus_result"} (see \code{\link{quercus_nf3}}
for element descriptions).  The \code{components} list may include up to
six named matrices: \code{Additive}, \code{Dominance}, \code{Environmental},
\code{Maternal}, \code{Paternal}, \code{Nuclear}.
}
\description{
Calls the \code{nf6} Pascal program to estimate up to six variance-covariance
components from a diallel cross with reciprocals.
}
\details{
The six causal components relate to Cockerham and Weir's (1977) observational
components as:
\itemize{
  \item Additive = \eqn{4\sigma^2_n}
  \item Dominance = \eqn{4\sigma^2_t}
  \item Maternal = \eqn{\sigma^2_m}
  \item Paternal = \eqn{\sigma^2_p}
  \item N x EN interaction = \eqn{\sigma^2_k}
  \item Environmental = \eqn{\sigma^2 - V_A/2 - 3V_D/4}
}
Components inestimable from the design must be constrained to zero.
}
\examples{
\dontrun{
compile_quercus()
demo_file <- system.file("extdata", "sibships.demo1", package = "quercus")
dat <- read_sibships(demo_file)
result <- quercus_nf6(dat)
print(result)
}
}
\references{
Cockerham, C. C. and Weir, B. S. (1977). Quadratic analyses of reciprocal
crosses. \emph{Biometrics}, 33(1), 187--203.

Shaw, R. G. (1987). Maximum-likelihood approaches applied to quantitative
genetics of natural populations. \emph{Evolution}, 41(4), 812--826.
}
\seealso{
\code{\link{quercus_nf3}}, \code{\link{compile_quercus}}
}
