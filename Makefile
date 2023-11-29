all: piless synth

piless: *.hs
	ghc -dynamic Main.hs -o piless

synth: *.hs
	ghc -O2 -dynamic SynthMain.hs -o synth


clean: rm *.hi *.o piless
