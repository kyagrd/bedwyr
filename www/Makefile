RCP = rsync -vrLtOCz --delete --stats \
      --exclude /Makefile --exclude /releases/ --exclude /doc/ --exclude /log/ \
      --exclude ".*.swp"

upload: bedwyr/pcmc/index.html
	$(RCP) . shell.gforge.inria.fr:/home/groups/slimmer/htdocs

bedwyr/pcmc/index.html: bedwyr/pcmc/index.php.html
	@php $< > $@
