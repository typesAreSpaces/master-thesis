iz3_file = open("iz3_results.txt", "r")

i = 0
for line in iz3_file.readlines():
    print(i)
    i+=1
    print(line)

iz3_file.close()
