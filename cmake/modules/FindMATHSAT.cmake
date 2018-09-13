# Looking for MATHSAT in CLANG_ANALYZER_MATHSAT_INSTALL_DIR
find_path(MATHSAT_INCLUDE_DIR NAMES mathsat.h
   NO_DEFAULT_PATH
   PATHS ${CLANG_ANALYZER_MATHSAT_INSTALL_DIR}/include
   PATH_SUFFIXES libmathsat mathsat
   )

find_library(MATHSAT_LIBRARIES NAMES mathsat libmathsat
   NO_DEFAULT_PATH
   PATHS ${CLANG_ANALYZER_MATHSAT_INSTALL_DIR}
   PATH_SUFFIXES lib bin
   )

find_program(MATHSAT_EXECUTABLE mathsat
   NO_DEFAULT_PATH
   PATHS ${CLANG_ANALYZER_MATHSAT_INSTALL_DIR}
   PATH_SUFFIXES bin
   )

# Find the required GMP library
find_library(GMP_LIBRARIES NAMES gmp libgmp
   PATHS ${CLANG_ANALYZER_MATHSAT_INSTALL_DIR}
   PATH_SUFFIXES lib
   )

# If MATHSAT has not been found in CLANG_ANALYZER_MATHSAT_INSTALL_DIR look in the default directories
find_path(MATHSAT_INCLUDE_DIR NAMES mathsat.h
   PATH_SUFFIXES libmathsat mathsat
   )

find_library(MATHSAT_LIBRARIES NAMES mathsat libmathsat
   PATH_SUFFIXES lib bin
   )

find_program(MATHSAT_EXECUTABLE mathsat
   PATH_SUFFIXES bin
   )

if(MATHSAT_INCLUDE_DIR AND MATHSAT_LIBRARIES AND MATHSAT_EXECUTABLE)
    execute_process (COMMAND ${MATHSAT_EXECUTABLE} -version
      OUTPUT_VARIABLE libmathsat_version_str
      ERROR_QUIET
      OUTPUT_STRIP_TRAILING_WHITESPACE)

    string(REGEX REPLACE "^MathSAT. version ([0-9.]+).*" "\\1"
           MATHSAT_VERSION_STRING "${libmathsat_version_str}")
    unset(libmathsat_version_str)
endif()

# handle the QUIETLY and REQUIRED arguments and set MATHSAT_FOUND to TRUE if
# all listed variables are TRUE
include(FindPackageHandleStandardArgs)
FIND_PACKAGE_HANDLE_STANDARD_ARGS(MATHSAT
                                  REQUIRED_VARS MATHSAT_LIBRARIES MATHSAT_INCLUDE_DIR GMP_LIBRARIES
                                  VERSION_VAR MATHSAT_VERSION_STRING)

mark_as_advanced(MATHSAT_INCLUDE_DIR MATHSAT_LIBRARIES GMP_LIBRARIES)
