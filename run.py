import battlecode as bc
import random
import sys
import traceback
import time
import math

import os
print(os.getcwd())

print("pystarting")

# A GameController is the main type that you talk to the game with.
# Its constructor will connect to a running game.
gc = bc.GameController()
directions = list(bc.Direction)

class Constants:
    LAUNCH_BY = 749
    DESIRED_WORKERS = 10
    DESIRED_FACTORIES = 5
    DIRECTION_CHANGES = [(0,1),(0,-1),(1,0),(-1,0),(1,1),(-1,-1),(1,-1),(-1,1)]
    REPLICATE_COST = 60
    WORKER_COST = 50
    OTHER_COST = 40
    ROCKET_COST = 150
    FACTORY_COST = 200
    HARVEST_AMOUNT = 3

class MyVars:
    workerCount = 0
    rangerCount = 0
    rocketCount = 0
    factoryCount = 0
    knightCount = 0
    mageCount = 0
    healerCount = 0
    sneakID = 0
    bestKarbLocs = []
    

print("pystarted")

# It's a good idea to try to keep your bots deterministic, to make debugging easier.
# determinism isn't required, but it means that the same things will happen in every thing you run,
# aside from turns taking slightly different amounts of time due to noise.
random.seed(6137)

my_team = gc.team()

#get initial variables and maps

gc.queue_research(bc.UnitType.Worker)

directions = list(bc.Direction)

earthMap = gc.starting_map(bc.Planet.Earth)
marsMap = gc.starting_map(bc.Planet.Mars)

earthWidth = earthMap.width
earthHeight = earthMap.height
marsWidth = marsMap.width
marsHeight = marsMap.height

#inverts a point on the map - used to estimate where the enemy will be
def invertPoint(point, planet):
    ptX = point[0]
    ptY = point[1]
    invertedX = earthMap.width - ptX
    invertedY = earthMap.height - ptY
    
    return (invertedX, invertedY)

#create maps of what places are passable and what places have karbonite on them
karboniteMapEarth = []
karboniteMapMars = []
passableMapEarth = []
passableMapMars = []

for i in range(earthHeight):
    karboniteMapEarth.append([0] * earthWidth)
    passableMapEarth.append([False] * earthWidth)
    

for i in range(marsHeight):
    karboniteMapMars.append([0] * marsWidth)
    passableMapMars.append([False] * marsWidth)
    
totalCount = 0

for i in range(earthWidth):
    for j in range(earthHeight):
        loc = bc.MapLocation(bc.Planet.Earth, j, i)
        karbCount = int(earthMap.initial_karbonite_at(loc))
        if(karbCount > 0):
            karboniteMapEarth[i][j] = int(earthMap.initial_karbonite_at(loc))
        passableMapEarth[i][j] = earthMap.is_passable_terrain_at(loc)
        
for i in range(marsWidth):
    for j in range(marsHeight):
        loc = bc.MapLocation(bc.Planet.Mars, i, j)
        karbCount = int(marsMap.initial_karbonite_at(loc))
        if(karbCount > 0):
            karboniteMapMars[i][j] = int(marsMap.initial_karbonite_at(loc))
        passableMapMars[i][j] = marsMap.is_passable_terrain_at(loc)

#get all of our starting points as well as the likely enemy starting points
startPoints = []
enemyStartPoints = []

for unit in gc.my_units():
    loc = unit.location.map_location()
    temp = (loc.x, loc.y)
    startPoints.append(temp)

for point in startPoints:
    enemyStartPoints.append(invertPoint(point, bc.Planet.Earth))
    
if len(gc.my_units()) > 2:
    #if we have 3 workers, we'll try to send one of them towards the enemies start to steal karbonite
    MyVars.sneakID = gc.my_units()[2].id
    
        
def onMap(loc):
    x = loc.x
    y = loc.y
    if loc.planet == bc.Planet.Earth:
        #print("Planet is Earth. Checking " + str(x) + "," + str(y))
        if x < 0 or x >= earthWidth or y < 0 or y >= earthHeight:
            #print("This is not on the map!")
            return False
    elif loc.planet == bc.Planet.Mars:
        if x < 0 or x >= marsWidth or y < 0 or y >= marsHeight:
            return False
    return True

#takes in a list of locations and finds the one "closest" to the destination based on a simple
#distance heuristic.  It also returns the index of the location it chose.
def lowestDist(locList, destination):
    lowest = 1000000
    choice = locList[0]
    index = 0
    for i in range(len(locList)):
        distance = pow(destination.x - locList[i][0], 2) + pow(destination.y - locList[i][1], 2)
        if distance < lowest:
            lowest = distance
            choice = locList[i]
            index = i
    return choice, index
    

#takes in a unit and a maplocation of a destination, then will return whatever step needs to be taken
#to reach the destination quickest
#current pathfinding algorithm
def BFS_firstStep(unit, destination):
    #get the position of the unit that we are trying to move.
        
    startT = int(round(time.time() * 1000))

    start = unit.location.map_location()
    
    startLoc = (start.x, start.y)
    destLoc = (destination.x, destination.y)
    
    planet = start.planet
    
    parent = {}
    queue = []
    visited = []
    queue.append(startLoc)
    while queue:
        node, index = lowestDist(queue, destination)
        queue.pop(index)
        visited.append(node)
        #print(node)
        #print("We've visited: ")
        #print(visited)
        if node == destLoc:
            #print("Reached end, reversing!")
            #starts a list which will track the entire path from the end to the exit
            #ends up reversing it and returning the location of the first step
            path = [destLoc]
            while path[-1] != startLoc:
                path.append(parent[path[-1]])
            path.reverse()
            print("BFS took " + str(int(round(time.time() * 1000)) - startT) + " time.")

            return start.direction_to(bc.MapLocation(planet, path[1][0], path[1][1]))
            
        for adjacent in getNeighbors(bc.MapLocation(planet, node[0], node[1])):
            adjLoc = (adjacent.x, adjacent.y)
            if adjLoc not in visited and adjLoc not in queue:
                #print(str(adjLoc) + " is not in visited!")
                parent[adjLoc] = node # <<<<< record its parent 
                queue.append(adjLoc)

def getNeighbors(location):
    
    neighbors = []
    
    for change in Constants.DIRECTION_CHANGES:
        tempLoc = bc.MapLocation(location.planet, location.x + change[0], location.y + change[1])
        #print("this neighbor is " + str(tempLoc.x) + "," + str(tempLoc.y))
        if onMap(tempLoc):
            #print("This is on the map!")
            if location.planet == bc.Planet.Earth:
                if earthMap.is_passable_terrain_at(tempLoc):
                    neighbors.append(tempLoc)
            elif location.planet == bc.Planet.Mars:
                if marsMap.is_passable_terrain_at(tempLoc):
                    neighbors.append(tempLoc)
    
    return neighbors

def nearbyKarb(location, planet):
    startT = int(round(time.time() * 1000))
    queue = [location]
    visited = []
    while queue:
        node = queue.pop(0)
        print("Checking " + str(node.x) + "," + str(node.y) + " for karbonite")
        visited.append(node)
        if planet == bc.Planet.Earth and karboniteMapEarth[node.y][node.x] > 0:
            print("nearbyKarb took " + str(int(round(time.time() * 1000)) - startT) + " time.")
            return node
        elif planet == bc.Planet.Mars and karboniteMapMars[node.y][node.x] > 0:
            print("nearbyKarb took " + str(int(round(time.time() * 1000)) - startT) + " time.")
            return node
        else:
            for adjacent in getNeighbors(node):
                if adjacent not in visited and adjacent not in queue:
                    #print(str(adjLoc) + " is not in visited!")
                    queue.append(adjacent)

def WorkerLogic(unit):
    ##priorities should be:
    # escape from enemies
    # replicate if we need more workers
    # harvest karbonite if near it / build structures if near it
    # move towards karbonite / nearest unbuilt structure
    
    #code to escape from enemies close
    
    if MyVars.workerCount < Constants.DESIRED_WORKERS and gc.karbonite() >= Constants.REPLICATE_COST:
        direct = getNeighbors(unit.location.map_location())
        for i in range(len(direct)):
            direction = unit.location.map_location().direction_to(direct[i])
            if gc.can_replicate(unit.id, direction):
                gc.replicate(unit.id, direction)
                MyVars.workerCount += 1
    else:
        #get nearby units and build them if possible
        nearby = gc.sense_nearby_units(unit.location.map_location(), 2)
        for tempUnit in nearby:
            if gc.can_build(unit.id, tempUnit.id):
                gc.build(unit.id, tempUnit.id)
                return
        #harvest any karbonite that is near us
        validLocs = getNeighbors(unit.location.map_location())
        validLocs.append(unit.location.map_location())
        for loc in validLocs:
            if karboniteMapEarth[loc.y][loc.x] > 0:
                directTo = unit.location.map_location().direction_to(loc)
                print(str(loc.x) + "," + str(loc.y) + " has karbonite!  Going to harvest.")
                if gc.can_harvest(unit.id, directTo):
                    gc.harvest(unit.id, directTo)
                    karboniteMapEarth[loc.y][loc.x] -= Constants.HARVEST_AMOUNT
                    return
        #try to build a factory blueprint if we don't have enough and have sufficient karbonite
        if gc.karbonite() > Constants.FACTORY_COST and MyVars.factoryCount < Constants.DESIRED_FACTORIES:
            for loc in validLocs:
                directTo = unit.location.map_location().direction_to(loc)
                if gc.can_blueprint(unit.id, bc.UnitType.Factory, directTo):
                    gc.blueprint(unit.id, bc.UnitType.Factory, directTo)
                    MyVars.factoryCount += 1
                    return
        
        #walk towards the best karbonite spot on the map
        destination = nearbyKarb(unit.location.map_location(), bc.Planet.Earth)
        myDirection = BFS_firstStep(unit, destination)
        if gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
            gc.move_robot(unit.id, myDirection)
            return
        
        
        
while True:
    # We only support Python 3, which means brackets around print()
    print('pyround:', gc.round(), 'time left:', gc.get_time_left_ms(), 'ms')
    # frequent try/catches are a good idea
    try:
        print("Current karbonite map is:")
        for i in range(len(karboniteMapEarth)):
            for j in range(len(karboniteMapEarth[i])):
                print (str(karboniteMapEarth[49-i][j]) + " ", end = '')
            print()
        if gc.round() > 25:
            Constants.HARVEST_AMOUNT = 4
        # walk through our units:
        #this code will primarily be used to determine 
        print("we have " + str(len(gc.my_units())) + " units.")
        for unit in gc.my_units():
            print("Working with unit " + str(unit.id))
            if unit.unit_type == bc.UnitType.Worker:
                WorkerLogic(unit)
                
            
            # first, factory logic
            elif unit.unit_type == bc.UnitType.Factory:
                garrison = unit.structure_garrison()
                if len(garrison) > 0:
                    d = random.choice(directions)
                    if gc.can_unload(unit.id, d):
                        print('unloaded a knight!')
                        gc.unload(unit.id, d)
                        continue
                elif gc.can_produce_robot(unit.id, bc.UnitType.Knight):
                    gc.produce_robot(unit.id, bc.UnitType.Knight)
                    print('produced a knight!')
                    continue

            # first, let's look for nearby blueprints to work on
            location = unit.location
            if location.is_on_map():
                nearby = gc.sense_nearby_units(location.map_location(), 2)
                for other in nearby:
                    if unit.unit_type == bc.UnitType.Worker and gc.can_build(unit.id, other.id):
                        gc.build(unit.id, other.id)
                        print('built a factory!')
                        # move onto the next unit
                        continue
                    if other.team != my_team and gc.is_attack_ready(unit.id) and gc.can_attack(unit.id, other.id):
                        print('attacked a thing!')
                        gc.attack(unit.id, other.id)
                        continue

            # okay, there weren't any dudes around
            # pick a random direction:
            d = random.choice(directions)

            # or, try to build a factory:
            if gc.karbonite() > bc.UnitType.Factory.blueprint_cost() and gc.can_blueprint(unit.id, bc.UnitType.Factory, d):
                gc.blueprint(unit.id, bc.UnitType.Factory, d)
            # and if that fails, try to move
            elif gc.is_move_ready(unit.id) and gc.can_move(unit.id, d):
                gc.move_robot(unit.id, d)

    except Exception as e:
        print('Error:', e)
        # use this to show where the error was
        traceback.print_exc()

    # send the actions we've performed, and wait for our next turn.
    gc.next_turn()

    # these lines are not strictly necessary, but it helps make the logs make more sense.
    # it forces everything we've written this turn to be written to the manager.
    sys.stdout.flush()
    sys.stderr.flush()
