piless: *.hs
	ghc Main.hs -o piless

clean: rm *.hi *.o piless
