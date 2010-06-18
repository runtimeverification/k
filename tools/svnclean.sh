echo 'The  following files will be deleted:'
svn status | grep "^?"
read -p "Press 'y' to confirm " -n 1
if [[ $REPLY =~ ^[Yy]$ ]]
then
  svn status | grep "^?" | awk -F " " '{print $2;}' |xargs rm
  printf "\nFiles deleted\n"
else
  printf "\nCommand aborted\n"
fi
