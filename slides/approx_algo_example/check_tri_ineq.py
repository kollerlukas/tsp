import itertools

c = [
  [0,2,3,3,3],
  [2,0,2,3,1],
  [3,2,0,3,2],
  [3,3,3,0,2],
  [3,1,2,2,0],
]

for x in range(0,5):
  for y in range(0,5):
    for z in range(0,5):
      if c[x][z] > c[x][y] + c[y][z]:
        print(f'c {x+1} {z+1} > c {x+1} {y+1} + c {y+1} {z+1}')

min_tour = []
min_cost = float('inf')
for p in list(itertools.permutations(range(0,5))):
  tour = list(p)
  tour.append(tour[0])
  cost = sum(list(map(lambda e: c[e[0]][e[1]], zip(tour[:-1],tour[1:]))))
  if cost < min_cost:
    min_tour = tour
    min_cost = cost

print(min_cost)
print(min_tour)
