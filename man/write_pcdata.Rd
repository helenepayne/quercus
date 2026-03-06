\name{write_pcdata}
\alias{write_pcdata}
\title{Write a pcdata Input File for pcrf1}
\usage{
write_pcdata(
  data,
  file = "pcdata",
  method = 2L,
  nchar = NULL,
  nfixed = 1L,
  feasibility = FALSE,
  start_values = NULL,
  constraints = NULL,
  g_constraints = NULL,
  trait_cols = NULL,
  fixed_cols = NULL,
  missing_value = -99
)
}
\arguments{
\item{data}{A data frame with pedigree and phenotype data for two populations.
The first fixed factor must be the population identifier (1 or 2).}

\item{file}{Path to write the output file.}

\item{method}{Integer; \code{1} for ML, \code{2} for REML (default).}

\item{nchar}{Integer; number of traits.}

\item{nfixed}{Integer; number of fixed factors including the population ID
(default \code{1}).}

\item{feasibility}{Logical; impose feasibility constraints.}

\item{start_values}{Optional numeric vector of starting values.}

\item{constraints}{Integer vector of component indices to constrain to zero.}

\item{g_constraints}{Integer vector of additive component indices to
constrain equal between populations.}

\item{trait_cols}{Phenotype column names or indices.}

\item{fixed_cols}{Fixed-factor column names or indices.}

\item{missing_value}{Missing data sentinel (default \code{-99}).}
}
\value{
Invisibly returns \code{file}.
}
\description{
Like \code{\link{write_sibships}} but adds the extra G-matrix constraint
line required by \code{pcrf1}.
}
\seealso{
\code{\link{write_sibships}}, \code{\link{quercus_pcrf1}}
}
