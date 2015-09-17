#!/bin/bash
# C++11
# Конструкторы и поля (по отдельности) должны быть уникальны в пределах datatype, других конфликтов быть не может

set -e

[ $# != 0 ] && echo "Usage: ${0##*/}" >&2 && exit 1

while IFS="" read -r LINE; do
	read -r SHORT_LINE <<< "$LINE"

	case "$SHORT_LINE" in
		"@datatype "*)
			read -r DATATYPE NAME <<< "$LINE"

			N=0

			printf "#include <utility>\\n"

			COPY=true
			MOVE=true

			while :; do
				if ! IFS="" read -r LINE; then
					echo "${0##*/}: @end expected" >&2
					exit 1
				fi

				read -r SHORT_LINE <<< "$LINE"

				case "$SHORT_LINE" in
					"@ctor "*)
						read -r CTOR CTOR_NAME ARGS <<< "$LINE"
						CTORS[N]="$CTOR_NAME"
						ARGVS[N]="$ARGS"
						N=$((N + 1))
						printf "// $SHORT_LINE\\n"
						;;
					"@nocopy")
						COPY=false
						printf "// $SHORT_LINE\\n"
						;;
					"@nomove")
						MOVE=false
						printf "// $SHORT_LINE\\n"
						;;
					"@end")
						break
						;;
				esac
			done

			printf "class $NAME{ public: enum class kind {"

			for ((I = 0; I != N - 1; ++I)){
				printf "${CTORS[I]}, "
			}

			printf "${CTORS[N - 1]}}; kind k; "

			for ((I = 0; I != N; ++I)){
				if [ -n "${ARGVS[I]}" ]; then
					(
						IFS=","

						for DECL in ${ARGVS[I]}; do
							IFS=" " read -r DECL <<< "$DECL"
							printf "$DECL; "
						done
					)
				fi
			}

			printf "$NAME () = default; "

			if ! "$COPY"; then
				printf "$NAME (const $NAME &) = delete; "
				printf "$NAME &operator= (const $NAME &) = delete; "
			fi

			if "$MOVE"; then
				printf "$NAME ($NAME &&) = default; "
				printf "$NAME &operator= ($NAME &&) = default; "
			else
				printf "$NAME ($NAME &&) = delete; "
				printf "$NAME &operator= ($NAME &&) = delete; "
			fi

			for ((I = 0; I != N; ++I)){
					if [ -z "${ARGVS[I]}" ]; then
						printf "make_${CTORS[I]} (void)"
					else
						printf "template <$(sed -e 's/[^,]*\([^0-9A-Z_a-z]\)\([0-9A-Z_a-z][0-9A-Z_a-z]*\) *,/typename \2_t,/g' \
							-e 's/[^,]*\([^0-9A-Z_a-z]\)\([0-9A-Z_a-z][0-9A-Z_a-z]*\) *$/typename \2_t/g' <<< "${ARGVS[I]}")> static $NAME "
						printf "make_${CTORS[I]} ($(sed -e 's/[^,]*\([^0-9A-Z_a-z]\)\([0-9A-Z_a-z][0-9A-Z_a-z]*\) *,/\2_t \&\&\2,/g' \
							-e 's/[^,]*\([^0-9A-Z_a-z]\)\([0-9A-Z_a-z][0-9A-Z_a-z]*\) *$/\2_t \&\&\2/g' <<< "${ARGVS[I]}"))"
					fi

					printf "{ $NAME result; result.k = kind::${CTORS[I]}; "

					(
						IFS=","

						for DECL in ${ARGVS[I]}; do
							FIELD="$(sed 's/^.*[^0-9A-Z_a-z]\([0-9A-Z_a-z][0-9A-Z_a-z]*\) *$/\1/' <<< "$DECL")"
							printf "result.$FIELD = std::forward <${FIELD}_t> ($FIELD); "
						done
					)

					printf "return result; }"
			}

			printf "};\\n"
			;;
		"@"*)
			echo "${0##*/}: wrong command" >&2
			exit 1
			;;
		*)
			printf '%s\n' "$LINE"
			;;
	esac
done
