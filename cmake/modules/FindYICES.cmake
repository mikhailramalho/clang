# Looking for YICES in CLANG_ANALYZER_YICES_INSTALL_DIR
find_path(YICES_INCLUDE_DIR NAMES yices.h
   NO_DEFAULT_PATH
   PATHS ${CLANG_ANALYZER_YICES_INSTALL_DIR}/include
   PATH_SUFFIXES libyices yices
   )

find_library(YICES_LIBRARIES NAMES yices libyices
   NO_DEFAULT_PATH
   PATHS ${CLANG_ANALYZER_YICES_INSTALL_DIR}
   PATH_SUFFIXES lib bin
   )

find_program(YICES_EXECUTABLE yices
   NO_DEFAULT_PATH
   PATHS ${CLANG_ANALYZER_YICES_INSTALL_DIR}
   PATH_SUFFIXES bin
   )

# Find GMP required
# TODO: improve this with a FindGMP.cmake script
find_library(GMP_LIBRARIES NAMES gmp libgmp
   PATHS ${CLANG_ANALYZER_YICES_INSTALL_DIR}
   PATH_SUFFIXES lib bin)

# If YICES has not been found in CLANG_ANALYZER_YICES_INSTALL_DIR look in the default directories
find_path(YICES_INCLUDE_DIR NAMES yices.h
   PATH_SUFFIXES libyices yices
   )

find_library(YICES_LIBRARIES NAMES yices libyices
   PATH_SUFFIXES lib bin
   )

find_program(YICES_EXECUTABLE yices
   PATH_SUFFIXES bin
   )

if(YICES_INCLUDE_DIR AND YICES_LIBRARIES AND YICES_EXECUTABLE)
    execute_process (COMMAND ${YICES_EXECUTABLE} --version
      OUTPUT_VARIABLE libyices_version_str
      ERROR_QUIET
      OUTPUT_STRIP_TRAILING_WHITESPACE)

    string(REGEX REPLACE "^Yices ([0-9.]+)\n.*" "\\1"
           YICES_VERSION_STRING "${libyices_version_str}")
    unset(libyices_version_str)
endif()

# handle the QUIETLY and REQUIRED arguments and set YICES_FOUND to TRUE if
# all listed variables are TRUE
include(FindPackageHandleStandardArgs)
FIND_PACKAGE_HANDLE_STANDARD_ARGS(YICES
                                  REQUIRED_VARS YICES_LIBRARIES GMP_LIBRARIES YICES_INCLUDE_DIR
                                  VERSION_VAR YICES_VERSION_STRING)

mark_as_advanced(YICES_INCLUDE_DIR YICES_LIBRARIES GMP_LIBRARIES)
