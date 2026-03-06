\name{write_sibships}
\alias{write_sibships}
\title{Write a sibships Input File for Quercus Analysis Programs}
\usage{
write_sibships(
  data,
  file = "sibships",
  method = 2L,
  nchar = NULL,
  nfixed = 0L,
  feasibility = FALSE,
  start_values = NULL,
  constraints = NULL,
  trait_cols = NULL,
  fixed_cols = NULL,
  missing_value = -99
)
}
\arguments{
\item{data}{A data frame with columns \code{id}, \code{father},
\code{mother}, optionally fixed-factor columns, and phenotype column(s).}

\item{file}{Path to write the output file.  If \code{NULL}, returns the
lines as a character vector.}

\item{method}{Integer; \code{1} for ML, \code{2} for REML (default).}

\item{nchar}{Integer; number of traits.  Inferred if \code{NULL}.}

\item{nfixed}{Integer; number of fixed factors (default \code{0}).}

\item{feasibility}{Logical; impose feasibility constraints (default
\code{FALSE}).}

\item{start_values}{Optional numeric vector of starting values.}

\item{constraints}{Integer vector of component indices to constrain to zero.}

\item{trait_cols}{Phenotype column names or indices.}

\item{fixed_cols}{Fixed-factor column names or indices.}

\item{missing_value}{Numeric sentinel for missing phenotypes (default
\code{-99}).}
}
\value{
Invisibly returns \code{file}, or the character vector of lines when
\code{file = NULL}.
}
\description{
Converts a pedigree data frame to the plain-text input format expected by
\code{nf3}, \code{nf6}, and \code{fend}.
}
\seealso{
\code{\link{read_sibships}}, \code{\link{write_pcdata}}
}
