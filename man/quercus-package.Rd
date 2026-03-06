\name{quercus-package}
\alias{quercus-package}
\alias{quercus}
\docType{package}
\title{quercus: Maximum Likelihood Analysis of Quantitative Genetic Data}
\description{
R interface to the Quercus programs for maximum likelihood (ML) and
restricted maximum likelihood (REML) estimation of genetic and environmental
variances and covariances from two-generation pedigree data with multivariate
phenotypic observations and fixed effects.
}
\details{
Four programs are available:
\tabular{ll}{
\code{\link{quercus_nf3}} \tab Three-component analysis for nested and
  parent-offspring designs.\cr
\code{\link{quercus_nf6}} \tab Six-component analysis for diallel crosses.\cr
\code{\link{quercus_pcrf1}} \tab Comparison of G matrices between two
  populations.\cr
\code{\link{quercus_fend}} \tab Determine minimum compile-time constants.\cr
}

Before first use, install the Free Pascal Compiler and run
\code{compile_quercus()}.
}
\references{
Shaw, R. G. (1987). Maximum-likelihood approaches applied to quantitative
genetics of natural populations. \emph{Evolution}, 41(4), 812--826.

Cockerham, C. C. and Weir, B. S. (1977). Quadratic analyses of reciprocal
crosses. \emph{Biometrics}, 33(1), 187--203.
}
\author{
Ruth G. Shaw and Frank H. Shaw
}
\keyword{package}
