
%.anm: %.anm.spec
	cd ../../.. && cargo run --release -- truanm $@ -o $<

all: \
	th12-embedded-bad-image-source.anm \
	th12-embedded-image-source.anm \
	th12-embedded-weird-format-source.anm \
	th12-multiple-match-source.anm \
	th12-multiple-same-source.anm \

