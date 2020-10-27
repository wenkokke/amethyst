#/bin/sh

# Neural network specification
NETWORK="$1"
shift

# Input query
QUERY="$1"
shift

# Temporary directory for files
TEMP=$(mktemp -d 2>/dev/null || mktemp -d -t 'amethyst')

# Save inputs to temporary files
echo "$NETWORK" > $TEMP/input.nnet
echo "$QUERY" > $TEMP/input.query

# Run Marabou
./vendor/Marabou/build/Marabou --input=$TEMP/input.nnet --input-query=$TEMP/input.query
