CC      ?= cc
CFLAGS  ?= -O2 -std=gnu11 -Wall -Wextra -fopenmp
LDLIBS  ?= -lm

all: ag_frvote libag_frvote.a external_caller

noize:noizy.c
	$(CC) $(CFLAGS) -o $@ $< $(LDLIBS)

keri:fr_simd.c
	$(CC) $(CFLAGS) -o $@ $< $(LDLIBS)

bbgs_kotter:bbgs_kotter.c
	$(CC) $(CFLAGS) -o $@ $< $(LDLIBS)

bbgs:bbgs.c
	$(CC) $(CFLAGS) -o $@ $< $(LDLIBS)

kotter: kotter.c
	$(CC) $(CFLAGS) -o $@ $< $(LDLIBS)

value: value.c
	$(CC) $(CFLAGS) -o $@ $< $(LDLIBS)

k2: bbgs_k.c
	$(CC) $(CFLAGS) -o $@ $< $(LDLIBS)

libag_frvote.a: ag_frvote_lib.o
	ar rcs $@ $^

ag_frvote_lib.o: noizy.c ag_frvote.h
	$(CC) $(CFLAGS) -DAG_FRVOTE_NO_MAIN -c -o $@ keri.c

external_caller: external_caller.c libag_frvote.a ag_frvote.h
	$(CC) $(CFLAGS) -o $@ external_caller.c libag_frvote.a $(LDLIBS)

test: all
	./test_api.sh

clean:
	rm -f ag_frvote ag_frvote_lib.o libag_frvote.a external_caller

.PHONY: all test clean