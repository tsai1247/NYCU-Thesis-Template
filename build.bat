xelatex -synctex=1 -shell-escape -interaction=nonstopmode main.tex
bibtex main.aux
xelatex -synctex=1 -shell-escape -interaction=nonstopmode main.tex
xelatex -synctex=1 -shell-escape -interaction=nonstopmode main.tex
@REM del *.aux 
@REM del *.log 
@REM del *.gz 
@REM del *.bbl 
@REM del *.blg 
@REM del *.lof 
@REM del *.lot 
@REM del *.toc 
@REM del *.out

