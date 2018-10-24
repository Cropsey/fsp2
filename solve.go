package main

import (
	"bufio"
	"fmt"
	"math"
	"os"
	"runtime"
	"sort"
	"strconv"
	"strings"
	"time"
	//"github.com/pkg/profile"
)

/* Notes:
 * - more identical flights with different prices can appear - filter during input reading?
 *   - we cannot assume any order of input (available testing data are sorted by day or by src, dst, day)
 * - simulated anealing seems to rock best in last challenge
 * - ending in the same area, not city
 * - index of the first day is 1, 0 has special meaning (flight occuring on every day)
 */

/* TODO:
 * - solution engine
 * - search for better solutions for whole time limit
 */

const MAX_CITIES int = 300
const MAX_AREAS int = 300
const MAX_DAYS int = 300
const MAX_FLIGHTS int = 27000000

type Day uint16
type City uint16
type Area uint16
type Money uint32

type Flight struct {
	From      City
	To        City
	FromArea  Area
	ToArea    Area
	Day       Day
	Cost      Money
	Heuristic Money
	Penalty   float64
}

type comm interface {
	send(r Solution) Money
	done()
}
type solutionComm struct {
	best        Solution
	searchedAll chan bool
	timeout     <-chan time.Time
}

func NewComm(timeout <-chan time.Time) *solutionComm {
	initBest := Solution{}
	initBest.totalCost = math.MaxInt32
	return &solutionComm{
		initBest,
		make(chan bool),
		timeout,
	}
}
func (c *solutionComm) send(r Solution) Money {
	bestCost := c.best.totalCost
	if bestCost < r.totalCost {
		return bestCost
	}

	flights := make([]*Flight, len(r.flights))
	copy(flights, r.flights)
	sort.Sort(byDay(flights))
	c.best = Solution{flights, r.totalCost}
	return r.totalCost
}
func (c *solutionComm) done() {
	c.searchedAll <- true
}
func (c *solutionComm) wait() {
	select {
	case <-c.searchedAll:
		return
	case <-c.timeout:
		return
	}
}

type partial struct {
	flights []*Flight
	visited []bool
	n       int
	cost    Money
}

func (p *partial) solution() Solution {
	return Solution{p.flights, p.cost}
}
func (p *partial) roundtrip() bool {
	ff := p.flights[0]
	lf := p.lastFlight()
	isHome := lf.To == ff.From
	return len(p.visited) == p.n && isHome
}
func (p *partial) fly(f *Flight) {
	p.visited[int(f.FromArea)] = true
	p.flights = append(p.flights, f)
	p.cost += f.Cost
}
func (p *partial) hasVisited(a Area) bool {
	return p.visited[a]
}
func (p *partial) lastFlight() *Flight {
	return p.flights[len(p.flights)-1]
}
func (p *partial) backtrack() {
	f := p.flights[len(p.flights)-1]
	p.visited[int(f.FromArea)] = false
	p.flights = p.flights[0 : len(p.flights)-1]
	p.cost -= f.Cost
}

type Greedy struct {
	graph       FlightIndices
	currentBest Money
}

func (d *Greedy) dfs(comm comm, partial *partial) {
	if partial.cost > d.currentBest {
		return
	}
	if partial.roundtrip() {
		d.currentBest = comm.send(partial.solution())
	}

	lf := partial.lastFlight()
	if partial.hasVisited(lf.ToArea) {
		return
	}

	//dst := d.graph.cityDayCost[lf.To][int(lf.Day+1)%d.graph.size]
	if d.graph.cityDayCost[lf.To] == nil {
		return
	}
	if d.graph.cityDayCost[lf.To][lf.Day+1] == nil {
		return
	}
	dst := d.graph.cityDayCost[lf.To][lf.Day+1]
	for _, f := range dst {
		partial.fly(f)
		d.dfs(comm, partial)
		partial.backtrack()
	}
}
func (d Greedy) Solve(comm comm, problem Problem) {
	if problem.length <= 1000 {
		flights := make([]*Flight, 0, problem.length)
		visited := make([]bool, problem.length, problem.length)
		partial := partial{flights, visited, problem.length, 0}

		dst := d.graph.cityDayCost[0][1]
		for _, f := range dst {
			//fmt.Println(dst)
			partial.fly(f)
			d.dfs(comm, &partial)
			partial.backtrack()
		}
		comm.done()
	} else {
		//not running
	}
}

func NewSolution(flights []*Flight) Solution {
	sort.Sort(byDay(flights))
	return Solution{flights, cost(flights)}
}

type Solution struct {
	flights   []*Flight
	totalCost Money
}

type LookupA struct {
	nameToIndex map[string]Area
	indexToName []string
}

type LookupC struct {
	nameToIndex map[string]City
	indexToName []string
}

type FlightIndices struct {
	areaDayCost [][][]*Flight // sorted by cost
	cityDayCost [][][]*Flight // sorted by cost
	//dayArea     [][][]*Flight
	//dayCity     [][][]*Flight
}

type AreaDb struct {
	cityToArea   map[City]Area
	areaToCities map[Area][]City
}

type Problem struct {
	flights []Flight
	indices FlightIndices
	//areas []Area
	areaDb     AreaDb
	areaLookup LookupA
	cityLookup LookupC
	start      City
	goal       Area
	length     int
	timeLimit  time.Duration
}

type byCost []*Flight

func (f byCost) Len() int {
	return len(f)
}
func (f byCost) Swap(i, j int) {
	f[i], f[j] = f[j], f[i]
}
func (f byCost) Less(i, j int) bool {
	return f[i].Cost < f[j].Cost
}

type byDay []*Flight

func (f byDay) Len() int {
	return len(f)
}
func (f byDay) Swap(i, j int) {
	f[i], f[j] = f[j], f[i]
}
func (f byDay) Less(i, j int) bool {
	return f[i].Day < f[j].Day
}

func min(a, b int) int {
	if a < b {
		return a
	}
	return b
}

func cityIndex(city string, l *LookupC) City {
	/* get index of city in lookup table or put it in the table and get index */
	ci, found := l.nameToIndex[city]
	if found {
		return ci
	}
	ci = City(len(l.nameToIndex))
	l.nameToIndex[city] = ci
	l.indexToName = append(l.indexToName, city)
	return ci
}

func areaIndex(area string, l *LookupA) Area {
	ai, found := l.nameToIndex[area]
	if found {
		return ai
	}
	ai = Area(len(l.nameToIndex))
	l.nameToIndex[area] = ai
	l.indexToName = append(l.indexToName, area)
	return ai
}

func LastIndexByte(s string, c byte) int {
	for i := len(s) - 1; i >= 0; i-- {
		if s[i] == c {
			return i
		}
	}
	return -1
}

func flightSplit(s string, r []string) {
	/* Splits lines of input into 4 parts
	   strictly expects format "{3}[A-Z] {3}[A-Z] \d \d"
	   WARNING: no checks are done at all */
	r[0] = s[:3]
	r[1] = s[4:7]
	pos2 := LastIndexByte(s, ' ')
	r[2] = s[8:pos2]
	r[3] = s[pos2+1:]
}

func createIndexAD(slice [][][]*Flight, from Area, day Day, flight *Flight) {
	if slice[from] == nil {
		slice[from] = make([][]*Flight, MAX_DAYS+1)
	}
	if slice[from][day] == nil {
		slice[from][day] = make([]*Flight, 0, MAX_CITIES*2) // is there a max number of flights from a city on a date?
	}
	slice[from][day] = append(slice[from][day], flight)
}

func createIndexCD(slice [][][]*Flight, from City, day Day, flight *Flight) {
	if slice[from] == nil {
		slice[from] = make([][]*Flight, MAX_DAYS+1)
	}
	if slice[from][day] == nil {
		slice[from][day] = make([]*Flight, 0, MAX_CITIES*2) // is there a max number of flights from a city on a date?
	}
	slice[from][day] = append(slice[from][day], flight)
}

func readInput(stdin *bufio.Scanner) (p Problem) {
	lookupC := &LookupC{make(map[string]City), make([]string, 0, MAX_CITIES)}
	lookupA := &LookupA{make(map[string]Area), make([]string, 0, MAX_AREAS)}
	areaDb := &AreaDb{make(map[City]Area), make(map[Area][]City)}
	flights := make([]Flight, 0, MAX_FLIGHTS)
	indices := &FlightIndices{make([][][]*Flight, MAX_AREAS),
		make([][][]*Flight, MAX_CITIES),
		//make([][][]*Flight, MAX_DAYS),
		//make([][][]*Flight, MAX_DAYS),
	}
	line := make([]string, 4)

	var src string
	var timeLimit time.Duration
	var length, i int
	var from, to City
	var fromArea, toArea Area
	var day Day
	var cost Money
	// read first line
	if stdin.Scan() {
		firstLine := strings.Split(stdin.Text(), " ")
		src = firstLine[1]
		length, _ = strconv.Atoi(firstLine[0])
		cityIndex(src, lookupC)
	}
	// read areas
	var area string
	var areaId Area
	var cityId City
	var cities []string
	var cityIds []City
	for i := 0; i < length; i++ {
		stdin.Scan()
		area = stdin.Text()
		stdin.Scan()
		cities = strings.Split(stdin.Text(), " ")
		areaId = areaIndex(area, lookupA)
		//cityIds = make([]City)
		for _, src := range cities {
			cityId = cityIndex(src, lookupC)
			areaDb.cityToArea[cityId] = areaId
			cityIds = append(cityIds, cityId)
		}
		areaDb.areaToCities[areaId] = cityIds

	}
	runtime.GC()
	// read flights
	for stdin.Scan() {
		flightSplit(stdin.Text(), line)
		i, _ = strconv.Atoi(line[2])
		day = Day(i)
		i, _ = strconv.Atoi(line[3])
		cost = Money(i)
		from = cityIndex(line[0], lookupC)
		to = cityIndex(line[1], lookupC)
		//fromArea = areaIndex(line[0], LookupA)
		//toArea = areaIndex(line[1], LookupA)
		fromArea = areaDb.cityToArea[from]
		toArea = areaDb.cityToArea[to]
		if from == City(0) && day != 1 {
			// ignore any flight from src city not on the first day
			// fmt.Fprintln(os.Stderr, "Dropping flight", l)
			continue
		}
		if day == 1 && from != City(0) {
			// also flights originating in different than home city are wasteful
			// fmt.Fprintln(os.Stderr, "Dropping flight", l)
			continue
		}
		if int(day) != 0 && int(day) != length && toArea == areaDb.cityToArea[0] {
			// get rid of flights to final destination on different than last day
			// fmt.Fprintln(os.Stderr, "Dropping", day, from, "->", to)
			continue
		}
		if int(day) == 0 {
			// this flight takes place on every day, we will generate all the flights instead
			for i := 1; i <= length; i++ {
				if toArea == areaDb.cityToArea[0] && i < length {
					// fmt.Fprintln(os.Stderr, "Dropping", i, from, "->", to, length)
					continue
				}
				f := Flight{from, to, fromArea, toArea, Day(i), cost, 0, 0.0}
				flights = append(flights, f)
				createIndexAD(indices.areaDayCost, fromArea, Day(i), &f)
				createIndexCD(indices.cityDayCost, from, Day(i), &f)
			}
			continue
		}

		f := Flight{from, to, fromArea, toArea, day, cost, 0, 0.0}
		flights = append(flights, f)
		createIndexAD(indices.areaDayCost, fromArea, day, &f)
		createIndexCD(indices.cityDayCost, from, day, &f)

		if math.Mod(float64(day), 10) == 0 {
			runtime.GC()
		}

	}
	if length <= 20 {
		timeLimit = 3
	} else if length <= 100 {
		timeLimit = 5
	} else {
		timeLimit = 15
	}

	for _, dayList := range indices.areaDayCost {
		for _, flightList := range dayList {
			sort.Sort(byCost(flightList))
		}
	}

	for _, dayList := range indices.cityDayCost {
		for _, flightList := range dayList {
			sort.Sort(byCost(flightList))
		}
	}

	return Problem{flights, *indices, *areaDb, *lookupA, *lookupC,
		City(0), areaDb.cityToArea[City(0)], length, timeLimit}
}

func cost(path []*Flight) Money {
	var cost Money
	for _, f := range path {
		cost += f.Cost
	}
	return cost
}

func printSolution(s Solution, p Problem) {
	fmt.Println(s.totalCost)
	for i := 0; i < p.length; i++ {
		fmt.Println(p.cityLookup.indexToName[s.flights[i].From],
			p.cityLookup.indexToName[s.flights[i].To],
			i+1,
			s.flights[i].Cost,
		)
	}
}

func main() {
	start_time := time.Now()
	//defer profile.Start(profile.MemProfile).Stop()
	p := readInput(bufio.NewScanner(os.Stdin))
	g := Greedy{p.indices, math.MaxInt32}
	timeout := time.After(p.timeLimit * time.Second - time.Since(start_time) - 20 * time.Millisecond)
	c := NewComm(timeout)
	go g.Solve(c, p)
	c.wait()

	printSolution(c.best, p)

	fmt.Fprintln(os.Stderr, "Ending after", time.Since(start_time))
}
