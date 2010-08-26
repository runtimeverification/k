dnl check whether integer types $1 and $2 are the same

AC_DEFUN([__CIL_CHECK_INTEGER_TYPE_TYPE], [
  if test -z "$real_type"; then
    AC_COMPILE_IFELSE(AC_LANG_SOURCE([
#include <stddef.h>
#include <wchar.h>
/* We define a prototype with one type and the function with
   another type.  This will result in compilation error
   unless the types are really identical. */
$2 foo($2 x);
$1 foo($1 x) { return x; }]),
    real_type='$2')
  fi
])


dnl check whether integer type $1 is the
dnl the signed or unsigned variant of $2

AC_DEFUN([__CIL_CHECK_INTEGER_TYPE_SIGNS], [
  __CIL_CHECK_INTEGER_TYPE_TYPE([$1], [$2])
  __CIL_CHECK_INTEGER_TYPE_TYPE([$1], [unsigned $2])
])


dnl set configuration macro $2 to a string representing
dnl the real integer type corresponding to typedef $1

AC_DEFUN([CIL_CHECK_INTEGER_TYPE], [
  AC_MSG_CHECKING([for real definition of $1])
  real_type=''
  __CIL_CHECK_INTEGER_TYPE_SIGNS([$1], int)
  __CIL_CHECK_INTEGER_TYPE_SIGNS([$1], long)
  __CIL_CHECK_INTEGER_TYPE_SIGNS([$1], short)
  __CIL_CHECK_INTEGER_TYPE_SIGNS([$1], char)
  if test -z "$real_type"; then
    AC_MSG_ERROR([cannot find definition of $1])
  fi
  AC_DEFINE_UNQUOTED([$2], "[$real_type]")
  AC_MSG_RESULT([$real_type])
])


# I find it useful to mark generated files as read-only so I don't
# accidentally edit them (and them lose my changes when ./configure
# runs again); I had originally done the chmod after AC_OUTPUT, but
# the problem is then the chmod doesn't run inside ./config.status

# CIL_CONFIG_FILES(filename)
# do AC_CONFIG_FILES(filename, chmod a-w filename)
define([CIL_CONFIG_FILES],
[{
  if test -f [$1].in; then
    AC_CONFIG_FILES([$1], chmod a-w [$1])
  else
    true
    #echo "skipping [$1] because it's not in this distribution"
  fi
}])
define([CIL_CONFIG_EXE_FILES],
[{
  if test -f [$1].in; then
    AC_CONFIG_FILES([$1], [chmod a-w,a+x $1])
  else
    true
    #echo "skipping [$1] because it's not in this distribution"
  fi
}])
