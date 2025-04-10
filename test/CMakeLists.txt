###############################################################################
# Top contributors (to current version):
#   Daniel Larraz, Mathias Preiner, Aina Niemetz
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# The build system configuration.
##

# Add target 'check', builds and runs
# > unit tests
# > regression tests of levels 0 and 1
# > api tests

set(ENV_PATH_CMD )
if(WIN32)
  # Set up a command to add DLL library paths to PATH
  set(ENV_PATH )
  list(APPEND ENV_PATH ${CMAKE_BINARY_DIR}\\src)
  list(APPEND ENV_PATH ${CMAKE_BINARY_DIR}\\src\\parser)
  list(APPEND ENV_PATH ${DEPS_BASE}\\bin)
  list(APPEND ENV_PATH $ENV{PATH})
  # Escape semicolons and backslashes
  string(REPLACE "\\" "\\\\" ENV_PATH "${ENV_PATH}")
  list(JOIN ENV_PATH "\;" ENV_PATH)
  set(ENV_PATH_CMD ${CMAKE_COMMAND} -E env "PATH=${ENV_PATH}")
endif()

add_custom_target(build-tests)

# Note: Do not add custom targets for running tests (regress, apitests,
# units) as dependencies to other run targets. This will result in executing
# tests multiple times. For example, if check would depend on regress it would
# first run the command of the regress target (i.e., run all regression tests)
# and afterwards run the command specified for the check target.
# Dependencies of check are added in the corresponding subdirectories.
add_custom_target(check
  COMMAND
    ctest --output-on-failure -LE "regress[3-4]" -j${CTEST_NTHREADS} $$ARGS
  DEPENDS
    build-tests)

#-----------------------------------------------------------------------------#
# Add subdirectories

add_subdirectory(regress)
add_subdirectory(api EXCLUDE_FROM_ALL)
add_subdirectory(binary EXCLUDE_FROM_ALL)
if(ENABLE_UNIT_TESTING)
  add_subdirectory(unit EXCLUDE_FROM_ALL)
endif()
