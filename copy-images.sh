#! /bin/bash
# Remove the {@docRoot} string in all Doxygen files
sed -i 's/{@docRoot}\///g' javadoc/*.html

# Copy the doc-files folder
cp -r ../core/src/doc-files javadoc/
