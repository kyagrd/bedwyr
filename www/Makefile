RCP = rsync -vrLtOCz --delete --stats \
      --exclude /Makefile --exclude /releases/ --exclude /doc/ --exclude /log/ \
      --exclude-from=./.rsync-filter --exclude ".*.swp"

upload: bedwyr/pcmc/Makefile.build
	@$(MAKE) -C $(<D) -f $(<F)
	$(RCP) . shell.gforge.inria.fr:/home/groups/slimmer/htdocs

clean:
	$(MAKE) -C bedwyr/pcmc clean
	@find . -name '*~' -exec rm -v {} \;
