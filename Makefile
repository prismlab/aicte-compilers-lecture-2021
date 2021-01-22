all: interp.c
	gcc -o interp.exe interp.c

clean:
	rm -f a.out *.o *~ *.exe
