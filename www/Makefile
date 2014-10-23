RCP = rsync -vrLtOCz --delete --stats \
      --exclude /Makefile --exclude /releases/ --exclude /doc/ --exclude /log/ \
      --exclude ".*.swp"

upload:
	$(MAKE) -C bedwyr/pcmc
	$(RCP) . shell.gforge.inria.fr:/home/groups/slimmer/htdocs

clean:
	$(MAKE) -C bedwyr/pcmc clean
	@find . -name '*~' -exec rm -v {} \;
