REPO=project-starch/capstone-sail
REV=$(git rev-parse HEAD)

echo "${REPO} ${REV}"
awk '/function +clause +execute *\(CAPSTONE_INSN/ { gsub(/\)/, "", $(NF-2)); gsub(/CAPSTONE_/, "", $(NF-2)); print $(NF-2), FILENAME, FNR;}' model/*.sail
