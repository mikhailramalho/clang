# Looking for CVC4 in CLANG_ANALYZER_CVC4_INSTALL_DIR
find_path(CVC4_INCLUDE_DIR NAMES cvc4.h
   NO_DEFAULT_PATH
   PATHS ${CLANG_ANALYZER_CVC4_INSTALL_DIR}/include
   PATH_SUFFIXES libcvc4 cvc4
   )

find_library(CVC4_LIBRARIES NAMES cvc4 libcvc4
   NO_DEFAULT_PATH
   PATHS ${CLANG_ANALYZER_CVC4_INSTALL_DIR}
   PATH_SUFFIXES lib bin
   )

find_program(CVC4_EXECUTABLE cvc4
   NO_DEFAULT_PATH
   PATHS ${CLANG_ANALYZER_CVC4_INSTALL_DIR}
   PATH_SUFFIXES bin
   )

# Find the required GMP library
find_library(GMP_LIBRARIES NAMES gmp libgmp
   PATHS ${CLANG_ANALYZER_CVC4_INSTALL_DIR}
   PATH_SUFFIXES lib
   )

# If CVC4 has not been found in CLANG_ANALYZER_CVC4_INSTALL_DIR look in the default directories
find_path(CVC4_INCLUDE_DIR NAMES cvc4.h
   PATH_SUFFIXES libcvc4 cvc4
   )

find_library(CVC4_LIBRARIES NAMES cvc4 libcvc4
   PATH_SUFFIXES lib bin
   )

find_program(CVC4_EXECUTABLE cvc4
   PATH_SUFFIXES bin
   )

if(CVC4_INCLUDE_DIR AND CVC4_LIBRARIES AND CVC4_EXECUTABLE)
    execute_process (COMMAND ${CVC4_EXECUTABLE} --version
      OUTPUT_VARIABLE libcvc4_version_str
      ERROR_QUIET
      OUTPUT_STRIP_TRAILING_WHITESPACE)

    string(REGEX REPLACE "^This is CVC4 version ([0-9.]+).*" "\\1"
           CVC4_VERSION_STRING "${libcvc4_version_str}")
    unset(libcvc4_version_str)
endif()

# handle the QUIETLY and REQUIRED arguments and set CVC4_FOUND to TRUE if
# all listed variables are TRUE
include(FindPackageHandleStandardArgs)
FIND_PACKAGE_HANDLE_STANDARD_ARGS(CVC4
                                  REQUIRED_VARS CVC4_LIBRARIES CVC4_INCLUDE_DIR GMP_LIBRARIES
                                  VERSION_VAR CVC4_VERSION_STRING)

mark_as_advanced(CVC4_INCLUDE_DIR CVC4_LIBRARIES GMP_LIBRARIES)
