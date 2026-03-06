#' Compile Quercus Pascal programs
#'
#' Compiles the Pascal source files bundled with the quercus package using
#' the Free Pascal Compiler (\code{fpc}). This must be run once before
#' using the analysis functions (\code{\link{quercus_nf3}},
#' \code{\link{quercus_nf6}}, \code{\link{quercus_pcrf1}},
#' \code{\link{quercus_fend}}).
#'
#' @param compiler Path to the Pascal compiler executable. Defaults to
#'   \code{fpc} (Free Pascal Compiler), which must be on your PATH. Install
#'   from \url{https://www.freepascal.org/}.
#' @param destdir Directory in which to store the compiled executables.
#'   Defaults to a per-user cache directory returned by
#'   \code{tools::R_user_dir("quercus", "cache")}.
#' @param force Logical; if \code{TRUE}, recompile even if executables
#'   already exist. Default \code{FALSE}.
#'
#' @return Invisibly returns the path to the directory containing the
#'   compiled executables.
#'
#' @examples
#' \dontrun{
#' compile_quercus()
#' }
#'
#' @export
compile_quercus <- function(compiler = Sys.which("fpc"),
                             destdir  = quercus_bin_dir(),
                             force    = FALSE) {
  if (!nzchar(compiler)) {
    stop(
      "Free Pascal Compiler (fpc) not found on PATH.\n",
      "Install it from https://www.freepascal.org/ or provide the path ",
      "via the 'compiler' argument."
    )
  }

  pascal_dir <- system.file("pascal", package = "quercus")
  if (!nzchar(pascal_dir)) {
    stop("Pascal source directory not found inside the quercus package.")
  }

  programs <- c("nf3", "nf6", "pcrf1", "fend")

  if (!dir.exists(destdir)) {
    dir.create(destdir, recursive = TRUE)
  }

  # nf3 depends on the nf3_constants unit.  Compile the unit first so FPC
  # can find it when building nf3.  Unit object files are written alongside
  # the source in pascal_dir (requires write permission there; falls back to
  # destdir via -FU).
  unit_src <- file.path(pascal_dir, "nf3_constants.p")
  if (file.exists(unit_src)) {
    message("Compiling nf3_constants unit ...")
    out <- system2(compiler,
                   args = c("-Fu", pascal_dir, "-FU", destdir, unit_src),
                   stdout = TRUE, stderr = TRUE)
    # A successfully compiled unit produces a .ppu file
    ppu <- file.path(destdir, "nf3_constants.ppu")
    if (!file.exists(ppu)) {
      stop(
        "Compilation of 'nf3_constants' unit failed.\n",
        "Compiler output:\n", paste(out, collapse = "\n")
      )
    }
    message("nf3_constants unit compiled successfully.")
  }

  for (prog in programs) {
    exe <- file.path(destdir, prog)
    src <- file.path(pascal_dir, paste0(prog, ".p"))

    if (!file.exists(src)) {
      warning("Pascal source not found for '", prog, "': ", src, " -- skipping.")
      next
    }

    if (!force && file.exists(exe)) {
      message(prog, " already compiled; skipping (use force = TRUE to recompile).")
      next
    }

    message("Compiling ", prog, " ...")
    # -Fu: unit search path (source), -FU: unit output path (.ppu/.o)
    out <- system2(compiler,
                   args = c("-Fu", pascal_dir, "-FU", destdir,
                             "-o", exe, src),
                   stdout = TRUE, stderr = TRUE)
    if (!file.exists(exe)) {
      stop(
        "Compilation of '", prog, "' failed.\n",
        "Compiler output:\n", paste(out, collapse = "\n")
      )
    }
    message(prog, " compiled successfully.")
  }

  invisible(destdir)
}

#' Return the path to the quercus compiled-binary cache directory
#' @keywords internal
quercus_bin_dir <- function() {
  tools::R_user_dir("quercus", "cache")
}

#' Find the path to a compiled Quercus executable
#'
#' Searches, in order: the user cache directory populated by
#' \code{\link{compile_quercus}}, any binaries bundled in \code{inst/bin},
#' and finally the system PATH.
#'
#' @param name Program name (one of \code{"nf3"}, \code{"nf6"},
#'   \code{"pcrf1"}, \code{"fend"}).
#' @return Absolute path to the executable.
#' @keywords internal
find_exe <- function(name) {
  # User-compiled cache
  cached <- file.path(quercus_bin_dir(), name)
  if (file.exists(cached)) return(cached)

  # Bundled pre-compiled binary (inst/bin/)
  bundled <- system.file("bin", name, package = "quercus")
  if (nzchar(bundled) && file.exists(bundled)) return(bundled)

  # System PATH
  on_path <- Sys.which(name)
  if (nzchar(on_path)) return(on_path)

  stop(
    "Executable '", name, "' not found.\n",
    "Run compile_quercus() to compile the Pascal programs first.\n",
    "Pascal sources are in: ",
    system.file("pascal", package = "quercus")
  )
}
