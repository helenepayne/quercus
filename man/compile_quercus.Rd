\name{compile_quercus}
\alias{compile_quercus}
\title{Compile Quercus Pascal Programs}
\usage{
compile_quercus(
  compiler = Sys.which("fpc"),
  destdir = quercus_bin_dir(),
  force = FALSE
)
}
\arguments{
\item{compiler}{Path to the Pascal compiler executable.  Defaults to
\code{fpc} (Free Pascal Compiler) on the system PATH.  Install from
\url{https://www.freepascal.org/}.}

\item{destdir}{Directory in which to store the compiled executables.
Defaults to \code{tools::R_user_dir("quercus", "cache")}.}

\item{force}{Logical; if \code{TRUE}, recompile even if executables already
exist.  Default \code{FALSE}.}
}
\value{
Invisibly returns the path to the directory containing the compiled
executables.
}
\description{
Compiles the Pascal source files bundled with the quercus package using the
Free Pascal Compiler (\code{fpc}).  Must be run once before using the
analysis functions.
}
\examples{
\dontrun{
compile_quercus()
# Force recompilation
compile_quercus(force = TRUE)
}
}
