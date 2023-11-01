set -e

# Cleanup
rm -f lib/redder-*.tar.gz

# MacOS
npm install
npm run clean && npm run build && npm run test
tar czvf lib/redder-macos.tar.gz  -C src/lib/bs/native redder.native


# Linux
# Copies package.json etc. and runs `npm install`.
docker build -t redder .

# Mounts only the lib and src volume and runs `npm run build`
docker run -it -v $PWD/lib:/redder/lib -v $PWD/src:/redder/src redder bash -c "npm run clean && npm run build"

tar czvf lib/redder-linux.tar.gz  -C src/lib/bs/native redder.native
