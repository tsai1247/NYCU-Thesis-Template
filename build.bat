del *.log
 
xelatex -synctex=1 -shell-escape -interaction=nonstopmode main.tex
bibtex main.aux
@REM xelatex -synctex=1 -shell-escape -interaction=nonstopmode main.tex
@REM xelatex -synctex=1 -shell-escape -interaction=nonstopmode main.tex
del *.aux 
del *.gz 
del *.bbl 
del *.blg 
del *.lof 
del *.lot 
del *.toc 
del *.out

