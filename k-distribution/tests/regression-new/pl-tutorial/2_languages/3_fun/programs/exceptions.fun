try (
  try (
    3 + throw(10) * 2
  ) catch(x) (
    throw(2*x) + 7
  )
) catch(x) (
  x + 1
)

// 21
