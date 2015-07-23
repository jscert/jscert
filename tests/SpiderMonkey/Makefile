HG_REPO=https://hg.mozilla.org/mozilla-central
HG_REVISION=4925a84c57cf

GIT_REPO=https://github.com/mozilla/gecko-dev.git
GIT_REVISION=f79e34d84fdb517b4cd17fbb1a1096bdb10f91d6

default: .tests.patched

mozilla-central:
#	hg clone -r ${HG_REVISION} ${HG_REPO} mozilla-central
#	git clone ${GIT_REPO} mozilla-central && cd mozilla-central && git checkout ${GIT_REvISION}
	cd /tmp && wget https://github.com/mozilla/gecko-dev/archive/${GIT_REVISION}.zip
	unzip -u /tmp/${GIT_REVISION}.zip '*/js/src/tests/*' '*/js/src/jit-test/*'
	rm /tmp/${GIT_REVISION}.zip
	mv gecko-dev-${GIT_REVISION} mozilla-central

links: tests jit-test
tests: mozilla-central
	ln -fs mozilla-central/js/src/tests
jit-test: mozilla-central
	ln -fs mozilla-central/js/src/jit-test

# Patching routine that stores a copy of the applied patch for automatic re-application on change
.tests.patched: tests.patch links
	if [ -e $@ ]; then patch -R -p0 < $<; fi
	cp $< $@
	patch -p0 < $@

clean:
	rm -Rf mozilla-central
	rm -f tests
	rm -f jit-test
	rm -f .tests.patched

.PHONY: all links clean
