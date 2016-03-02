all: map

map: map.stg
	../../../dist/build/stg/stg map.stg
	gcc map.c ../../../cbits/rts.c -I../../../cbits/
