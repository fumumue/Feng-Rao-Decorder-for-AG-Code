CC ?= cc
CFLAGS ?= -O2 -std=c11 -Wall -Wextra -Werror

all: bbgs_newton

bbgs_newton: bbgs_newton.c
	$(CC) $(CFLAGS) -o $@ $<

test: bbgs_newton
	./run_tests.sh

clean:
	rm -f bbgs_newton bbgs_newton_san test_run_* san_* *.o

.PHONY: all test clean
