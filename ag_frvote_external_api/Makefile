# Unified Codes build file
# Usage:
#   make                         build with OpenMP
#   make OPENMP=                 build without OpenMP
#   make clean                   remove generated executable

CC       ?= cc
CFLAGS   ?= -O2 -std=gnu11 -Wall -Wextra
OPENMP   ?= -fopenmp
LDLIBS   ?= -lm
TARGET   := unified_codes
SOURCE   := unified_codes.c

.PHONY: all clean help

all: $(TARGET)

$(TARGET): $(SOURCE)
	$(CC) $(CFLAGS) $(OPENMP) -o $@ $< $(LDFLAGS) $(LDLIBS)

clean:
	rm -f $(TARGET)

help:
	@echo 'make          : build unified_codes (OpenMP enabled)'
	@echo 'make OPENMP=  : build without OpenMP'
	@echo 'make clean   : remove the executable'
