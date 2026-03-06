\name{read_sibships}
\alias{read_sibships}
\title{Read a sibships-Format File into a Data Frame}
\usage{
read_sibships(file, nfixed = 0L, nchar = NULL, missing_value = -99)
}
\arguments{
\item{file}{Path to a \code{sibships}-format file.}

\item{nfixed}{Integer; number of fixed-factor columns (default \code{0}).}

\item{nchar}{Integer; number of phenotype columns.  Inferred from the
header if \code{NULL}.}

\item{missing_value}{Numeric sentinel for missing data (default \code{-99}).}
}
\value{
A data frame with columns \code{id}, \code{father}, \code{mother},
optionally \code{fixed_1} \ldots \code{fixed_k}, and \code{trait_1}
\ldots \code{trait_p}.  Missing phenotype sentinels are replaced with
\code{NA}.
}
\description{
Parses a plain-text \code{sibships} file (the input format for the Quercus
programs) and returns the data as an R data frame.
}
\examples{
\dontrun{
demo_file <- system.file("extdata", "sibships.demo1", package = "quercus")
dat <- read_sibships(demo_file)
head(dat)
}
}
\seealso{
\code{\link{write_sibships}}
}
