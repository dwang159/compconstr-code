all: fact

fact: fact.stg
	../../../dist/build/stg/stg fact.stg
	gcc fact.c ../../../cbits/rts.c -I../../../cbits/
