TARGET=Blu

all:

build: alex happy ghc

#bnfc:
	#bnfc --haskell $(TARGET).cf

alex:
	alex -g --info=Lex$(TARGET)Info.txt Lex$(TARGET).x

happy:
	happy -gca --info=Par$(TARGET)Info.txt Par$(TARGET).y

ghc:
	ghc --make Test$(TARGET).hs -o Test$(TARGET)

.IGNORE: demo
demo:
	./Test$(TARGET) < tests/ex1_good.blu
	./Test$(TARGET) < tests/ex1_lexer_error.blu
	./Test$(TARGET) < tests/ex1_parser_error.blu
	./Test$(TARGET) < tests/ex1_typecheck_error.blu
	./Test$(TARGET) < tests/ex2_good.blu
	./Test$(TARGET) < tests/ex2_typecheck_error.blu
	./Test$(TARGET) < tests/ex3_good.blu
	./Test$(TARGET) < tests/ex3_typecheck_error.blu
	./Test$(TARGET) < tests/ex4_good.blu
	./Test$(TARGET) < tests/ex4_typecheck_error.blu
	./Test$(TARGET) < tests/ex5_good.blu
	./Test$(TARGET) < tests/ex5_typecheck_error.blu

clean:
	-rm -f *.log *.aux *.hi *.o *.dvi
