CC ?= cc
CFLAGS ?= -O2 -std=c11 -Wall -Wextra -Wpedantic

all: bbgs_e2_basic

bbgs_e2_basic: bbgs_e2_basic.c
	$(CC) $(CFLAGS) -o $@ $<

check: bbgs_e2_basic
	./bbgs_e2_basic --n 3 --errors 2 --trials 100 --seed 61114
	./bbgs_e2_basic --n 5 --errors 3 --trials 100 --seed 61114
	./bbgs_e2_basic --n 7 --errors 4 --trials 100 --seed 61114

clean:
	rm -f bbgs_e2_basic

.PHONY: all check clean
