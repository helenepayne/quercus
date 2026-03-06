\name{quercus_fend}
\alias{quercus_fend}
\title{Determine Minimum Array-Dimension Constants for a Dataset}
\usage{
quercus_fend(
  data,
  nchar = NULL,
  nfixed = 0L,
  trait_cols = NULL,
  fixed_cols = NULL,
  workdir = NULL,
  exe = NULL,
  verbose = FALSE
)
}
\arguments{
\item{data}{A data frame with pedigree and phenotype data.}

\item{nchar}{Integer; number of traits.}

\item{nfixed}{Integer; number of fixed factors.}

\item{trait_cols}{Phenotype column names or indices.}

\item{fixed_cols}{Fixed-factor column names or indices.}

\item{workdir}{Working directory.  A temporary directory by default.}

\item{exe}{Path to the \code{fend} executable.}

\item{verbose}{Print program output.}
}
\value{
A list with:
\describe{
  \item{\code{raw}}{Character vector of the full Topend output.}
  \item{\code{constants}}{Named integer vector of minimum constants
    (\code{nvarcov}, \code{maxnparm}, \code{nf}, \code{p}, \code{sibs},
    \code{rhsibs}, \code{fsibs}, \code{hsibs}, \code{rfsibs},
    \code{pos}).}
  \item{\code{families}}{Data frame with columns \code{family} and
    \code{size}.}
}
}
\description{
Calls the \code{fend} Pascal program to determine the minimum values
required for the compile-time array-dimension constants of \code{nf3} or
\code{nf6}.  Run this before recompiling for a new dataset.
}
\examples{
\dontrun{
compile_quercus()
demo_file <- system.file("extdata", "sibships.demo1", package = "quercus")
dat <- read_sibships(demo_file)
info <- quercus_fend(dat)
info$constants
}
}
\seealso{
\code{\link{quercus_nf3}}, \code{\link{compile_quercus}}
}
