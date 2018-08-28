# Looking for BOOLECTOR in CLANG_ANALYZER_BOOLECTOR_INSTALL_DIR
find_path(BOOLECTOR_INCLUDE_DIR NAMES boolector.h
   NO_DEFAULT_PATH
   PATHS ${CLANG_ANALYZER_BOOLECTOR_INSTALL_DIR}/include
   PATH_SUFFIXES libboolector boolector
   )

find_library(BOOLECTOR_LIBRARIES NAMES boolector libboolector
   NO_DEFAULT_PATH
   PATHS ${CLANG_ANALYZER_BOOLECTOR_INSTALL_DIR}
   PATH_SUFFIXES lib bin
   )

find_program(BOOLECTOR_EXECUTABLE boolector
   NO_DEFAULT_PATH
   PATHS ${CLANG_ANALYZER_BOOLECTOR_INSTALL_DIR}
   PATH_SUFFIXES bin
   )

# Find LINGELING required 
find_library(LGL_LIBRARIES NAMES lgl liblgl
   PATHS ${CLANG_ANALYZER_BOOLECTOR_INSTALL_DIR}
   PATH_SUFFIXES lib bin)

# If BOOLECTOR has not been found in CLANG_ANALYZER_BOOLECTOR_INSTALL_DIR look in the default directories
find_path(BOOLECTOR_INCLUDE_DIR NAMES boolector.h
   PATH_SUFFIXES libboolector boolector
   )

find_library(BOOLECTOR_LIBRARIES NAMES boolector libboolector
   PATH_SUFFIXES lib bin
   )

find_program(BOOLECTOR_EXECUTABLE boolector
   PATH_SUFFIXES bin
   )

if(BOOLECTOR_INCLUDE_DIR AND BOOLECTOR_LIBRARIES AND BOOLECTOR_EXECUTABLE)
    execute_process (COMMAND ${BOOLECTOR_EXECUTABLE} --version
      OUTPUT_VARIABLE libboolector_version_str
      ERROR_QUIET
      OUTPUT_STRIP_TRAILING_WHITESPACE)

    string(REGEX REPLACE "([0-9.]+)-.*" "\\1"
           BOOLECTOR_VERSION_STRING "${libboolector_version_str}")
    unset(libboolector_version_str)
endif()

# handle the QUIETLY and REQUIRED arguments and set BOOLECTOR_FOUND to TRUE if
# all listed variables are TRUE
include(FindPackageHandleStandardArgs)
FIND_PACKAGE_HANDLE_STANDARD_ARGS(BOOLECTOR
                                  REQUIRED_VARS BOOLECTOR_LIBRARIES LGL_LIBRARIES BOOLECTOR_INCLUDE_DIR
                                  VERSION_VAR BOOLECTOR_VERSION_STRING)

mark_as_advanced(BOOLECTOR_INCLUDE_DIR BOOLECTOR_LIBRARIES LGL_LIBRARIES)
