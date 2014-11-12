#include <iostream>

const int red = 0;
const int green = 1;
const int white = 2;
const int blue = 3;
const int yellow = 4;

const int british = 5;
const int swedish = 6;
const int danish = 7;
const int norwegian = 8;
const int german = 9;

const int tea = 10;
const int coffee = 11;
const int water = 12;
const int beer = 13;
const int milk = 14;

const int prince = 15;
const int blends = 16;
const int pallmall = 17;
const int bluemasters = 18;
const int dunhill = 19;

const int dog = 20;
const int cat = 21;
const int bird = 22;
const int horse = 23;
const int fish = 24;

inline int lives(int x, int y) {return x+5*y;}
inline int color(int x, int y) {return x+5*y;}
inline int drinks(int x, int y) {return x+5*y;}
inline int cigars(int x, int y) {return x+5*y;}
inline int pets(int x, int y) {return x+5*y;}

using namespace std;

// Generate DIMACS format CNF formula for Einstein's puzzle
int main()
{
    for(int i = 1; i <= 5; ++i)
    {
        cout << "color(" << i << ",red): " << color(i,red) << endl;
    }
    
    for(int i = 1; i <= 5; ++i)
    {
        cout << "color(" << i << ",green): " << color(i,green) << endl;
    }

    for(int i = 1; i <= 5; ++i)
    {
        cout << "color(" << i << ",white): " << color(i,white) << endl;
    }

    for(int i = 1; i <= 5; ++i)
    {
        cout << "color(" << i << ",blue): " << color(i,blue) << endl;
    }

    for(int i = 1; i <= 5; ++i)
    {
        cout << "color(" << i << ",yellow): " << color(i,yellow) << endl;
    }

    for(int i = 1; i <= 5; ++i)
    {
        cout << "lives(" << i << ",british): " << lives(i,british) << endl;
    }
    
    for(int i = 1; i <= 5; ++i)
    {
        cout << "lives(" << i << ",swedish): " << lives(i,swedish) << endl;
    }

    for(int i = 1; i <= 5; ++i)
    {
        cout << "lives(" << i << ",danish): " << lives(i,danish) << endl;
    }

    for(int i = 1; i <= 5; ++i)
    {
        cout << "lives(" << i << ",norwegian): " << lives(i,norwegian) << endl;
    }

    for(int i = 1; i <= 5; ++i)
    {
        cout << "lives(" << i << ",german): " << lives(i,german) << endl;
    }

    for(int i = 1; i <= 5; ++i)
    {
        cout << "drinks(" << i << ",tea): " << drinks(i,tea) << endl;
    }
    
    for(int i = 1; i <= 5; ++i)
    {
        cout << "drinks(" << i << ",coffee): " << drinks(i,coffee) << endl;
    }

    for(int i = 1; i <= 5; ++i)
    {
        cout << "drinks(" << i << ",water): " << drinks(i,water) << endl;
    }

    for(int i = 1; i <= 5; ++i)
    {
        cout << "drinks(" << i << ",beer): " << drinks(i,beer) << endl;
    }

    for(int i = 1; i <= 5; ++i)
    {
        cout << "drinks(" << i << ",milk): " << drinks(i,milk) << endl;
    }

    for(int i = 1; i <= 5; ++i)
    {
        cout << "cigars(" << i << ",prince): " << cigars(i,prince) << endl;
    }
    
    for(int i = 1; i <= 5; ++i)
    {
        cout << "cigars(" << i << ",blends): " << cigars(i,blends) << endl;
    }

    for(int i = 1; i <= 5; ++i)
    {
        cout << "cigars(" << i << ",pallmall): " << cigars(i,pallmall) << endl;
    }

    for(int i = 1; i <= 5; ++i)
    {
        cout << "cigars(" << i << ",bluemasters): " << cigars(i,bluemasters) << endl;
    }

    for(int i = 1; i <= 5; ++i)
    {
        cout << "cigars(" << i << ",dunhill): " << cigars(i,dunhill) << endl;
    }

    for(int i = 1; i <= 5; ++i)
    {
        cout << "pets(" << i << ",dog): " << pets(i,dog) << endl;
    }
    
    for(int i = 1; i <= 5; ++i)
    {
        cout << "pets(" << i << ",cat): " << pets(i,cat) << endl;
    }

    for(int i = 1; i <= 5; ++i)
    {
        cout << "pets(" << i << ",bird): " << pets(i,bird) << endl;
    }

    for(int i = 1; i <= 5; ++i)
    {
        cout << "pets(" << i << ",horse): " << pets(i,horse) << endl;
    }

    for(int i = 1; i <= 5; ++i)
    {
        cout << "pets(" << i << ",fish): " << pets(i,fish) << endl;
    }
    return 0;
}
