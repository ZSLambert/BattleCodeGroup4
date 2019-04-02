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

class Memory:
    destinations = {}
    combat_dest = {} #used by ranger logic for now 

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
    CHANGE_FROM_DIRECT = {
        bc.Direction.Center: (0,0),
        bc.Direction.South: (0,-1),
        bc.Direction.North: (0,1),
        bc.Direction.East: (1,0),
        bc.Direction.West: (-1,0),
        bc.Direction.Southeast: (1,-1),
        bc.Direction.Southwest: (-1,-1),
        bc.Direction.Northeast: (1,1),
        bc.Direction.Northwest: (-1,1)
    }
    DESTINATION_REACHED = bc.MapLocation(bc.Planet.Earth, -10, -10)
    RANGER_VISION = 70
    WKH_VISION = 50
    MAGE_VISION = 30
    RANGER_RANGE = 50
    MH_RANGE = 30
    KNIGHT_RANGE = 2

class MyVars:
    workerCount = 0
    rangerCount = 0
    rocketCount = 0
    factoryCount = 0
    knightCount = 0
    mageCount = 0
    healerCount = 0
    

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

print("Earth is " + str(earthWidth) + "x" + str(earthHeight))

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

#create the shells of the maps
for i in range(earthWidth):
    karboniteMapEarth.append([0] * earthHeight)
    passableMapEarth.append([False] * earthHeight)
    

for i in range(marsWidth):
    karboniteMapMars.append([0] * marsHeight)
    passableMapMars.append([False] * marsHeight)
    
totalCount = 0

#add in numbers/booleans for where karbonite/passable terrain is.
for i in range(earthWidth):
    for j in range(earthHeight):
        print("Working with point " + str(i) + "," + str(j))
        loc = bc.MapLocation(bc.Planet.Earth, i, j)
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
    Memory.combat_dest[invertPoint(point, bc.Planet.Earth)]
    
#determines whether a map location is on the map based on its x and y coordinates  
def onMap(loc):
    x = loc.x
    y = loc.y
    if loc.planet == bc.Planet.Earth:
        if x < 0 or x >= earthWidth or y < 0 or y >= earthHeight:
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
    
    #print("Trying to get from " + str(startLoc) + " to " + str(destLoc))
    
    planet = start.planet
    
    parent = {}
    queue = []
    visited = []
    queue.append(startLoc)
    while queue:
        #to intelligently choose nodes, get the one with the lowest straight line distance to destination, then remove that node from the queue.
        node, index = lowestDist(queue, destination)
        queue.pop(index)
        visited.append(node)
        if node == destLoc:
            #starts a list which will track the entire path from the end to the exit
            #ends up reversing it and returning the location of the first step
            path = [destLoc]
            while path[-1] != startLoc:
                path.append(parent[path[-1]])
            path.reverse()
            print("BFS took " + str(int(round(time.time() * 1000)) - startT) + " time.")
            #debugging in case we ever have the same destination as start point
            if len(path) == 1:
                return bc.Direction.Center
            return start.direction_to(bc.MapLocation(planet, path[1][0], path[1][1]))
            
        for adjacent in getNeighbors(bc.MapLocation(planet, node[0], node[1])):
            adjLoc = (adjacent.x, adjacent.y)
            if adjLoc not in visited and adjLoc not in queue:
                parent[adjLoc] = node # <<<<< record the parent of the node - used to get the path
                queue.append(adjLoc)
        #current bugFix - hoping to remove in the future - handles cases where we are trying to reach an unreachable destination.
        return bc.Direction.Center

def getNeighbors(location):
    
    neighbors = []
    #goes through all the different changes that could be applied to a position, and adds them to our list if they have passable terrain
    for change in Constants.DIRECTION_CHANGES:
        tempLoc = bc.MapLocation(location.planet, location.x + change[0], location.y + change[1])
        if onMap(tempLoc):
            if location.planet == bc.Planet.Earth:
                if earthMap.is_passable_terrain_at(tempLoc):
                    neighbors.append(tempLoc)
            elif location.planet == bc.Planet.Mars:
                if marsMap.is_passable_terrain_at(tempLoc):
                    neighbors.append(tempLoc)
    
    return neighbors

#greedy BFS to find the closest location with karbonite to our initial location.
def nearbyKarb(location, planet):
    startT = int(round(time.time() * 1000))
    queue = [location]
    visited = []
    while queue:
        node = queue.pop(0)
        visited.append(node)
        if planet == bc.Planet.Earth and karboniteMapEarth[node.x][node.y] > 0:
            print("nearbyKarb took " + str(int(round(time.time() * 1000)) - startT) + " time.")
            return node
        elif planet == bc.Planet.Mars and karboniteMapMars[node.x][node.y] > 0:
            print("nearbyKarb took " + str(int(round(time.time() * 1000)) - startT) + " time.")
            return node
        else:
            for adjacent in getNeighbors(node):
                if adjacent not in visited and adjacent not in queue:
                    #print(str(adjLoc) + " is not in visited!")
                    queue.append(adjacent)

#given a unit and a direction, returns the location of the unit moved in that direction.
def locFromDirect(unit, direction):
    location = unit.location.map_location()
    change = Constants.CHANGE_FROM_DIRECT[direction]
    return bc.MapLocation(location.planet, location.x + change[0], location.y + change[1])

def WorkerLogic(unit):
    ##priorities should be:
    # escape from enemies
    # replicate if we need more workers
    # harvest karbonite if near it / build structures if near it
    # move towards karbonite / nearest unbuilt structure
    
    #code to escape from enemies close
    
    #if we have reached our destination, change this units destination to a placeholder representing
    #that it has been reached.
    try:
        if unit.location.map_location() == Memory.destinations[unit.id]:
            Memory.destinations[unit.id] = Constants.DESTINATION_REACHED
    except:
        #do nothing - here so that we don't get an error if the destination hasn't been reached
        placeHolder = True
    
    #if we don't have enough workers, 
    if MyVars.workerCount < Constants.DESIRED_WORKERS and gc.karbonite() >= Constants.REPLICATE_COST:
        direct = getNeighbors(unit.location.map_location())
        for i in range(len(direct)):
            direction = unit.location.map_location().direction_to(direct[i])
            if gc.can_replicate(unit.id, direction):
                gc.replicate(unit.id, direction)
                MyVars.workerCount += 1
    else:
        #get locations which are passable nearby
        validLocs = getNeighbors(unit.location.map_location())
        
        #get nearby units and build them if possible
        nearby = gc.sense_nearby_units(unit.location.map_location(), 2)
        for tempUnit in nearby:
            if gc.can_build(unit.id, tempUnit.id):
                gc.build(unit.id, tempUnit.id)
                return
        #harvest any karbonite that is near us
        for direct in directions:
            if gc.can_harvest(unit.id, direct):
                gc.harvest(unit.id, direct)
                harvestedLoc = locFromDirect(unit, direct)
                if unit.location.map_location().planet == bc.Planet.Earth:
                    karboniteMapEarth[harvestedLoc.x][harvestedLoc.y] = gc.karbonite_at(harvestedLoc)
                else:
                    karboniteMapMars[harvestedLoc.x][harvestedLoc.y] = gc.karbonite_at(harvestedLoc)
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
        try:
            #get the destination that this unit is supposed to be going to
            destination = Memory.destinations[unit.id]
            #if we already reached that destination: get a new one
            if destination == Constants.DESTINATION_REACHED:
                print("Destination was reached already so getting a new one")
                destination = nearbyKarb(unit.location.map_location(), bc.Planet.Earth)
                Memory.destinations[unit.id] = destination
        except:
            #this will only happen the first time a destination is generated for a spot
            print("There was no destination stored for unit " + str(unit.id) + " so we had to make one!")
            destination = nearbyKarb(unit.location.map_location(), bc.Planet.Earth)
            Memory.destinations[unit.id] = destination
            
        #move in the correct direction to get to our destination if possible.
        myDirection = BFS_firstStep(unit, destination) 
        if gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
            gc.move_robot(unit.id, myDirection)
            return
        
def mage_logic():
    print("")


def healer_logic():  
    print("")

def ranger_logic():

    #sense enemies
    nearby = gc.sense_nearby_units(location.map_location(), Constants.RANGER_VISION)

    for place in nearby:
        if place.team != my_team and gc.is_attack_ready(unit.id) and gc.can_attack(unit.id, place.id):
            print("Attacked a unit!")
            gc.attack(unit.id, place.id)
            continue
    for place in nearby:
        if place.team != my_team and not gc.can_attack(unit.id, place.id):
            myDirection = BFS_firstStep(unit, place.location.map_location())
            if gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
                gc.move_robot(unit.id, myDirection)
                continue
    try:
        #could we change this to find enemy Karbonite? 
          destination = Memory.combat_dest[unit.id]
          if destination == Constants.DESTINATION_REACHED:
                print("Destination was reached already so getting a new one")
                destination = nearbyKarb(unit.location.map_location(), bc.Planet.Earth)
                Memory.combat_dest[unit.id] = destination

    #have enemy walk toward enemy start 
    myDirection = BFS_firstStep(unit, destination)
    if gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
        gc.move_robot(unit.id, myDirection)
    
while True:
    # We only support Python 3, which means brackets around print()
    print('pyround:', gc.round(), 'time left:', gc.get_time_left_ms(), 'ms')
    # frequent try/catches are a good idea
    try:
        if(gc.round() % 50 == 0):
            print("Current karbonite map is:")
            for i in range(len(karboniteMapEarth)):
                for j in range(len(karboniteMapEarth[i])):
                    print (str(karboniteMapEarth[49-i][j]) + " ", end = '')
                print()
        if gc.round() > 25:
            Constants.HARVEST_AMOUNT = 4
        # walk through our units:
        #this code will primarily be used to determine 
        #print("we have " + str(len(gc.my_units())) + " units.")
        for unit in gc.my_units():
            #print("Working with unit " + str(unit.id))
            if unit.unit_type == bc.UnitType.Worker:
                WorkerLogic(unit)
            elif unit.unit_type == bc.UnitType.Ranger:
                #In the future, we will use ranger logic here.  Basic logic so we attack:
                location = unit.location
                if location.is_on_map():
                    ranger_logic()
                    
            
            # first, factory logic
            elif unit.unit_type == bc.UnitType.Factory:
                garrison = unit.structure_garrison()
                if len(garrison) > 0:
                    d = random.choice(directions)
                    if gc.can_unload(unit.id, d):
                        print('unloaded a ranger!')
                        gc.unload(unit.id, d)
                        continue
                elif gc.can_produce_robot(unit.id, bc.UnitType.Ranger):
                    gc.produce_robot(unit.id, bc.UnitType.Ranger)
                    print('produced a ranger!')
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