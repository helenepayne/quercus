#' Determine minimum array-dimension constants for a dataset
#'
#' Calls the \code{fend} Pascal program, which makes a first pass through a
#' \code{sibships}-format dataset and reports the minimum values needed for
#' the compile-time constants of \code{nf3} or \code{nf6}.  Run this before
#' recompiling the Pascal programs for a new dataset.
#'
#' The output is written to a file called \code{Topend} in \code{workdir}
#' and is also returned as a character vector.
#'
#' Before calling this function, compile the Pascal programs with
#' \code{\link{compile_quercus}}.
#'
#' @inheritParams quercus_nf3
#'
#' @return A list with elements:
#' \describe{
#'   \item{\code{raw}}{Character vector of the full Topend output.}
#'   \item{\code{constants}}{Named integer vector of the minimum constants
#'     extracted from the output (\code{nvarcov}, \code{maxnparm},
#'     \code{nf}, \code{p}, \code{sibs}, \code{rhsibs}, \code{fsibs},
#'     \code{hsibs}, \code{rfsibs}, \code{pos}).}
#'   \item{\code{families}}{Data frame with columns \code{family} and
#'     \code{size}.}
#' }
#'
#' @examples
#' \dontrun{
#' compile_quercus()
#' demo_file <- system.file("extdata", "sibships.demo1", package = "quercus")
#' dat <- read_sibships(demo_file)
#' info <- quercus_fend(dat)
#' info$constants
#' }
#'
#' @export
quercus_fend <- function(data,
                          nchar      = NULL,
                          nfixed     = 0L,
                          trait_cols = NULL,
                          fixed_cols = NULL,
                          workdir    = NULL,
                          exe        = NULL,
                          verbose    = FALSE) {

  exe     <- exe %||% find_exe("fend")
  workdir <- workdir %||% tempfile("quercus_fend_")
  if (!dir.exists(workdir)) dir.create(workdir, recursive = TRUE)

  # fend reads from "sibships" using method=2 (REML) but the method flag
  # does not affect what fend does; write with REML as a safe default.
  sibships_file <- file.path(workdir, "sibships")
  write_sibships(
    data       = data,
    file       = sibships_file,
    method     = 2L,
    nchar      = nchar,
    nfixed     = nfixed,
    trait_cols = trait_cols,
    fixed_cols = fixed_cols
  )

  out     <- run_quercus(exe, workdir, verbose)
  topend  <- file.path(workdir, "Topend")

  raw <- if (file.exists(topend)) readLines(topend) else out

  list(
    raw       = raw,
    constants = parse_topend_constants(raw),
    families  = parse_topend_families(raw)
  )
}


#' Extract named constants from Topend output
#' @keywords internal
parse_topend_constants <- function(lines) {
  keys <- c("nvarcov", "nf", "p", "sibs", "rhsibs", "fsibs",
            "hsibs", "rfsibs", "pos")
  vals <- integer(length(keys))
  names(vals) <- keys

  for (k in keys) {
    pat  <- paste0("\\b", k, "\\s*=?\\s*([0-9]+)")
    hits <- grep(pat, lines, ignore.case = TRUE, value = TRUE)
    if (length(hits) > 0L) {
      m <- regmatches(hits[1L], regexpr("[0-9]+$", hits[1L]))
      if (length(m) > 0L) vals[k] <- as.integer(m)
    }
  }

  # maxnparm appears as "Total number of (co)variances" line
  mp_hit <- grep("maxnparm|Total number.*nf3", lines, ignore.case = TRUE,
                 value = TRUE)
  if (length(mp_hit) > 0L) {
    m <- regmatches(mp_hit[1L], regexpr("[0-9]+", mp_hit[1L]))
    if (length(m) > 0L) vals["maxnparm"] <- as.integer(m)
  }

  # pos appears at the end
  pos_hit <- grep("pos\\s*\\)", lines, ignore.case = TRUE, value = TRUE)
  if (length(pos_hit) > 0L) {
    m <- regmatches(pos_hit[1L], regexpr("[0-9]+", pos_hit[1L]))
    if (length(m) > 0L) vals["pos"] <- as.integer(m)
  }

  vals
}


#' Extract family-size table from Topend output
#' @keywords internal
parse_topend_families <- function(lines) {
  fam_lines <- grep("^family\\s+[0-9]+\\s+has\\s+[0-9]+",
                    lines, ignore.case = TRUE, value = TRUE)
  if (length(fam_lines) == 0L) return(data.frame(family = integer(0),
                                                   size   = integer(0)))
  nums <- lapply(fam_lines, function(ln) {
    as.integer(regmatches(ln, gregexpr("[0-9]+", ln))[[1L]])
  })
  data.frame(
    family = vapply(nums, `[[`, integer(1L), 1L),
    size   = vapply(nums, `[[`, integer(1L), 2L)
  )
}
