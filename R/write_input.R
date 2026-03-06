#' Write a sibships input file for Quercus analysis programs
#'
#' Converts a pedigree data frame to the plain-text input format expected by
#' \code{nf3}, \code{nf6}, and \code{fend}.
#'
#' The input data frame must contain the columns \code{id}, \code{father}, and
#' \code{mother} (integer IDs; founders have father = mother = 0). Any
#' additional columns are treated first as fixed-factor levels (if
#' \code{nfixed > 0}) and then as phenotypic traits.  Missing phenotypic
#' values should be encoded as \code{NA} in the data frame; they are
#' written as \code{missing_value} in the output.
#'
#' @param data A data frame with columns \code{id}, \code{father},
#'   \code{mother}, optionally \code{nfixed} fixed-factor columns, and one or
#'   more phenotype columns.
#' @param file Path to write the output file.  If \code{NULL}, the lines are
#'   returned as a character vector instead of writing to disk.
#' @param method Integer; \code{1} for maximum likelihood, \code{2} for
#'   restricted maximum likelihood (default).
#' @param nchar Integer; number of traits to analyse.  If \code{NULL},
#'   inferred automatically from \code{trait_cols}.
#' @param nfixed Integer; number of categorical fixed factors beyond the
#'   grand mean (default \code{0}).
#' @param feasibility Logical; whether to impose feasibility constraints so
#'   that variance-covariance matrices remain positive definite (default
#'   \code{FALSE}).
#' @param start_values Optional numeric vector of starting values for the
#'   variance components.  If supplied, it is written on a new line after
#'   line 1.
#' @param constraints Optional integer vector of component indices to
#'   constrain to zero.  See the Quercus documentation for the ordering of
#'   components.
#' @param trait_cols Character vector (or integer indices) identifying the
#'   phenotype columns in \code{data}.  If \code{NULL}, all columns after
#'   \code{id}/\code{father}/\code{mother} and any fixed-factor columns are
#'   used.
#' @param fixed_cols Character vector (or integer indices) identifying the
#'   fixed-factor columns in \code{data}.  If \code{NULL} and
#'   \code{nfixed > 0}, the first \code{nfixed} columns after the pedigree
#'   columns are used.
#' @param missing_value Numeric sentinel written for \code{NA} phenotypes
#'   (default \code{-99}).
#'
#' @return Invisibly returns \code{file} (or the character vector of lines
#'   when \code{file = NULL}).
#'
#' @examples
#' \dontrun{
#' demo_file <- system.file("extdata", "sibships.demo1", package = "quercus")
#' dat <- read_sibships(demo_file)
#' write_sibships(dat, file = tempfile())
#' }
#'
#' @export
write_sibships <- function(data,
                            file         = "sibships",
                            method       = 2L,
                            nchar        = NULL,
                            nfixed       = 0L,
                            feasibility  = FALSE,
                            start_values = NULL,
                            constraints  = NULL,
                            trait_cols   = NULL,
                            fixed_cols   = NULL,
                            missing_value = -99) {

  method   <- as.integer(method)
  nfixed   <- as.integer(nfixed)
  feasible <- as.integer(isTRUE(feasibility))
  startval <- as.integer(!is.null(start_values))

  base_cols <- c("id", "father", "mother")
  if (!all(base_cols %in% names(data))) {
    stop("'data' must contain columns 'id', 'father', and 'mother'.")
  }

  remaining <- setdiff(names(data), base_cols)

  if (is.null(fixed_cols) && nfixed > 0L) {
    fixed_cols <- remaining[seq_len(nfixed)]
  }
  if (is.null(trait_cols)) {
    trait_cols <- setdiff(remaining, fixed_cols)
  }
  if (is.null(nchar)) {
    nchar <- length(trait_cols)
  }

  lines <- character()

  # Line 1: analysis options
  lines <- c(lines, paste(method, nchar, nfixed, feasible, startval))

  # Optional starting values
  if (!is.null(start_values)) {
    lines <- c(lines, paste(format(start_values, scientific = FALSE),
                             collapse = " "))
  }

  # Constraint line
  if (is.null(constraints) || length(constraints) == 0L) {
    lines <- c(lines, "0")
  } else {
    lines <- c(lines,
               paste(c(length(constraints), as.integer(constraints)),
                     collapse = " "))
  }

  # Individual data rows
  for (i in seq_len(nrow(data))) {
    row   <- data[i, , drop = FALSE]
    parts <- c(as.integer(row[["id"]]),
               as.integer(row[["father"]]),
               as.integer(row[["mother"]]))

    if (nfixed > 0L && length(fixed_cols) > 0L) {
      parts <- c(parts, as.integer(unlist(row[fixed_cols])))
    }

    trait_vals <- as.numeric(unlist(row[trait_cols[seq_len(nchar)]]))
    trait_vals[is.na(trait_vals)] <- missing_value
    parts <- c(parts, trait_vals)

    lines <- c(lines, paste(parts, collapse = " "))
  }

  # Terminal record
  lines <- c(lines, "0")

  if (is.null(file)) return(lines)
  writeLines(lines, file)
  invisible(file)
}


#' Write a pcdata input file for pcrf1
#'
#' Like \code{\link{write_sibships}} but adds the extra G-matrix constraint
#' line required by \code{pcrf1}.  The first fixed factor must be the
#' population identifier (integer 1 or 2).
#'
#' @param g_constraints Optional integer vector of additive component indices
#'   to constrain equal between the two populations.
#' @inheritParams write_sibships
#'
#' @return Invisibly returns \code{file}.
#'
#' @export
write_pcdata <- function(data,
                          file          = "pcdata",
                          method        = 2L,
                          nchar         = NULL,
                          nfixed        = 1L,
                          feasibility   = FALSE,
                          start_values  = NULL,
                          constraints   = NULL,
                          g_constraints = NULL,
                          trait_cols    = NULL,
                          fixed_cols    = NULL,
                          missing_value = -99) {

  method   <- as.integer(method)
  nfixed   <- as.integer(nfixed)
  feasible <- as.integer(isTRUE(feasibility))
  startval <- as.integer(!is.null(start_values))

  base_cols <- c("id", "father", "mother")
  if (!all(base_cols %in% names(data))) {
    stop("'data' must contain columns 'id', 'father', and 'mother'.")
  }

  remaining <- setdiff(names(data), base_cols)

  if (is.null(fixed_cols) && nfixed > 0L) {
    fixed_cols <- remaining[seq_len(nfixed)]
  }
  if (is.null(trait_cols)) {
    trait_cols <- setdiff(remaining, fixed_cols)
  }
  if (is.null(nchar)) {
    nchar <- length(trait_cols)
  }

  lines <- character()
  lines <- c(lines, paste(method, nchar, nfixed, feasible, startval))

  if (!is.null(start_values)) {
    lines <- c(lines, paste(format(start_values, scientific = FALSE),
                             collapse = " "))
  }

  if (is.null(constraints) || length(constraints) == 0L) {
    lines <- c(lines, "0")
  } else {
    lines <- c(lines,
               paste(c(length(constraints), as.integer(constraints)),
                     collapse = " "))
  }

  # G-matrix constraint line (unique to pcrf1)
  if (is.null(g_constraints) || length(g_constraints) == 0L) {
    lines <- c(lines, "0")
  } else {
    lines <- c(lines,
               paste(c(length(g_constraints), as.integer(g_constraints)),
                     collapse = " "))
  }

  for (i in seq_len(nrow(data))) {
    row   <- data[i, , drop = FALSE]
    parts <- c(as.integer(row[["id"]]),
               as.integer(row[["father"]]),
               as.integer(row[["mother"]]))

    if (nfixed > 0L && length(fixed_cols) > 0L) {
      parts <- c(parts, as.integer(unlist(row[fixed_cols])))
    }

    trait_vals <- as.numeric(unlist(row[trait_cols[seq_len(nchar)]]))
    trait_vals[is.na(trait_vals)] <- missing_value
    parts <- c(parts, trait_vals)

    lines <- c(lines, paste(parts, collapse = " "))
  }

  lines <- c(lines, "0")
  writeLines(lines, file)
  invisible(file)
}


#' Read a sibships-format file into a data frame
#'
#' Parses the plain-text pedigree/phenotype file used as input to the Quercus
#' programs and returns it as an R data frame.
#'
#' @param file Path to a \code{sibships}-format file.
#' @param nfixed Integer; number of fixed-factor columns (default \code{0}).
#' @param nchar Integer; number of phenotype columns.  If \code{NULL},
#'   inferred from the first data line.
#' @param missing_value Numeric sentinel used in the file for missing data
#'   (default \code{-99}).
#'
#' @return A data frame with columns \code{id}, \code{father}, \code{mother},
#'   optionally \code{fixed_1} \ldots \code{fixed_k}, and \code{trait_1}
#'   \ldots \code{trait_p}. \code{NA} is substituted for the missing sentinel.
#'
#' @export
read_sibships <- function(file, nfixed = 0L, nchar = NULL,
                           missing_value = -99) {
  raw <- readLines(file)

  # Strip header lines (line 1, optional start values, constraint line)
  hdr     <- strsplit(trimws(raw[1L]), "\\s+")[[1L]]
  method  <- as.integer(hdr[1L])
  nc_file <- as.integer(hdr[2L])
  if (is.null(nchar)) nchar <- nc_file

  # Determine how many header lines to skip
  startval_flag <- as.integer(hdr[5L])
  skip <- if (startval_flag == 1L) 3L else 2L   # line1 + [startvals] + constraints

  data_lines <- raw[seq(skip + 1L, length(raw))]
  data_lines <- data_lines[nzchar(trimws(data_lines))]
  # Drop terminal "0"
  data_lines <- data_lines[data_lines != "0"]

  rows <- lapply(data_lines, function(ln) {
    as.numeric(strsplit(trimws(ln), "\\s+")[[1L]])
  })

  mat <- do.call(rbind, rows)
  n_cols <- ncol(mat)

  col_names <- c("id", "father", "mother")
  if (nfixed > 0L) {
    col_names <- c(col_names, paste0("fixed_", seq_len(nfixed)))
  }
  col_names <- c(col_names, paste0("trait_", seq_len(nchar)))

  if (length(col_names) < n_cols) {
    col_names <- c(col_names,
                   paste0("col_", seq(length(col_names) + 1L, n_cols)))
  }

  df <- as.data.frame(mat[, seq_len(length(col_names)), drop = FALSE])
  names(df) <- col_names

  df[["id"]]     <- as.integer(df[["id"]])
  df[["father"]] <- as.integer(df[["father"]])
  df[["mother"]] <- as.integer(df[["mother"]])

  for (tc in grep("^trait_", names(df), value = TRUE)) {
    df[[tc]][df[[tc]] <= missing_value] <- NA_real_
  }

  df
}
