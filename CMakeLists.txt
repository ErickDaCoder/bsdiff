cmake_minimum_required(VERSION 3.25)
project(BSdiff)

set(CMAKE_C_STANDARD 99)

add_library(bzip2 STATIC
        bz2/blocksort.c
        bz2/bzip2.c
        bz2/bzip2recover.c
        bz2/bzlib.c
        bz2/compress.c
        bz2/crctable.c
        bz2/decompress.c
        bz2/huffman.c
        bz2/mk251.c
        bz2/randtable.c
        bz2/unzcrash.c
)
include_directories(bz2)

add_library(libbsdiff STATIC bsdiff.c bspatch.c)

add_executable(BSdiffp bsdiff.c)
target_compile_definitions(BSdiffp PRIVATE BSDIFF_EXECUTABLE)
target_link_libraries(BSdiffp PRIVATE bzip2)

add_executable(BSpatchp bspatch.c)
target_compile_definitions(BSpatchp PRIVATE BSPATCH_EXECUTABLE)
target_link_libraries(BSpatchp PRIVATE bzip2)
