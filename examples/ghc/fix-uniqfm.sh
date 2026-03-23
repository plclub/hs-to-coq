#!/bin/bash
# Post-processing for UniqFM.v after generation
# Fixes phantom type parameters and Word64Map references

cd "$(dirname "$0")"

# Fix Word64Map/Word64Set references
sed -i 's/GHC\.Data\.Word64Map\.Internal\./Data.IntMap.Internal./g; s/GHC\.Data\.Word64Map\.Strict\.Internal\./Data.IntMap.Internal./g; s/GHC\.Data\.Word64Set\.Internal\./Data.IntSet.Internal./g; s/Word64Map/IntMap/g; s/Word64Set/IntSet/g' lib/UniqFM.v

# Fix phantom type parameters
python3 -c "
import re
with open('lib/UniqFM.v', 'r') as f:
    content = f.read()

# Pattern: {k : Type} ... {key : k} -> remove {k : Type}, change {key : k} to {key : Type}
# Handle different variable names for the kind variable
# Simple case: {k : Type} directly followed by {key : k}
content = re.sub(r'\{k\s*:\s*Type\}\s*\{key\s*:\s*k\}', '{key : Type}', content)
content = re.sub(r'\{inst_k\s*:\s*Type\}\s*\{inst_key\s*:\s*inst_k\}', '{inst_key : Type}', content)

# Case with intervening binders: {k : Type} {other binders} {key : k}
# Remove standalone {k : Type} and change {key : k} to {key : Type}
content = re.sub(r'\{k\s*:\s*Type\}\s+', '', content)
content = re.sub(r'\{key\s*:\s*k\}', '{key : Type}', content)

# Handle k1/k2 patterns (strictMapUFM, unsafeCastUFMKey)
content = re.sub(r'\{k1\s*:\s*Type\}\s+', '', content)
content = re.sub(r'\{k2\s*:\s*Type\}\s+', '', content)
content = re.sub(r'\{key1\s*:\s*k1\}', '{key1 : Type}', content)
content = re.sub(r'\{key2\s*:\s*k2\}', '{key2 : Type}', content)
content = re.sub(r'\{k2\s*:\s*k1\}', '{k2 : Type}', content)

# inst_ variants
content = re.sub(r'\{inst_k\s*:\s*Type\}\s+', '', content)
content = re.sub(r'\{inst_key\s*:\s*inst_k\}', '{inst_key : Type}', content)

with open('lib/UniqFM.v', 'w') as f:
    f.write(content)
"

echo "UniqFM.v post-processing done"
