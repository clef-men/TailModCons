awk '
	$1 ~ /^#/ {
	}
	NF == 3 && $2 == "->" {
		print "-Q "$1" "$3
	}
	$1 ~ /^-/ {
		for (i = 1 ; i <= NF ; i++)
			print "-arg "$i
	}
	NF == 1 && $1 ~ /.v$/ {
		cmd = "find $(dirname '\''"$1"'\'') -name $(basename '\''"$1"'\'')"
		while ((cmd | getline output) > 0)
			print output
		close cmd
	}
' __CoqProject > _CoqProject
