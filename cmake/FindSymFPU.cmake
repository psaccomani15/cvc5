###############################################################################
# Top contributors (to current version):
#   Gereon Kremer, Mathias Preiner, Alex Ozdemir
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Find SymFPU
# SymFPU_FOUND - should always be true
# SymFPU - interface target for the SymFPU headers
##

find_path(SymFPU_INCLUDE_DIR NAMES symfpu/core/unpackedFloat.h)

set(SymFPU_FOUND_SYSTEM FALSE)
if(SymFPU_INCLUDE_DIR)
  # Found SymFPU to be installed system-wide
  set(SymFPU_FOUND_SYSTEM TRUE)
endif()

if(NOT SymFPU_FOUND_SYSTEM)
  check_ep_downloaded("SymFPU-EP")
  if(NOT SymFPU-EP_DOWNLOADED)
    check_auto_download("SymFPU" "")
  endif()

  include(ExternalProject)
  include(deps-helper)

  set(SymFPU_COMMIT "e6ac3af9c2c574498ea171c957425b407625448b")
  set(SymFPU_CHECKSUM "823aa663fcc2f6844ae5e9ea83ceda4ed393cdb3dadefce9b3c7c41cd0f4f702")

  ExternalProject_Add(
    SymFPU-EP
    ${COMMON_EP_CONFIG}
    URL https://github.com/cvc5/symfpu/archive/${SymFPU_COMMIT}.tar.gz
    URL_HASH SHA256=${SymFPU_CHECKSUM}
    CONFIGURE_COMMAND ""
    BUILD_COMMAND ""
    INSTALL_COMMAND ${CMAKE_COMMAND} -E copy_directory <SOURCE_DIR>/core
                    <INSTALL_DIR>/include/symfpu/core
    COMMAND ${CMAKE_COMMAND} -E copy_directory <SOURCE_DIR>/utils
            <INSTALL_DIR>/include/symfpu/utils
  )

  set(SymFPU_INCLUDE_DIR "${DEPS_BASE}/include/")
endif()

set(SymFPU_FOUND TRUE)

add_library(SymFPU INTERFACE IMPORTED GLOBAL)
set_target_properties(
  SymFPU PROPERTIES INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${SymFPU_INCLUDE_DIR}"
)

mark_as_advanced(SymFPU_FOUND)
mark_as_advanced(SymFPU_FOUND_SYSTEM)
mark_as_advanced(SymFPU_INCLUDE_DIR)

if(SymFPU_FOUND_SYSTEM)
  message(STATUS "Found SymFPU: ${SymFPU_INCLUDE_DIR}")
else()
  message(STATUS "Building SymFPU: ${SymFPU_INCLUDE_DIR}")
  add_dependencies(SymFPU SymFPU-EP)
endif()
