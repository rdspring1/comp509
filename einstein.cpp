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
    for(int k = 0; k < 5; ++k)
    {
        for(int c1 = 1; c1 <= 5; ++c1)
        {
             cout << color(c1, k) << " "; // every house has a color
        }
        cout << "0" << endl;

        for(int c1 = 1; c1 <= 5; ++c1)
        {
            for(int c2 = 1; c2 < c1; ++c2)
            {
                cout << "-" << color(c1,k) << " -" << color(c2, k) << " 0" << endl; // use color only once
            }
    
            for(int k1 = 0; k1 < 5; ++k1)
            {
                if(k1 != k)
                {
                    cout << "-" << color(c1,k) << " -" << color(c1, k1) << " 0" << endl; // only one color per house
                }
            }
        }
    } 

    cout << lives(1, norwegian) << " 0" << endl; // house 1 and norwegian
    cout << color(2, blue) << " 0" << endl; // house 2 and blue
    cout << drinks(3, milk) << " 0" << endl; // house 3 and milk

    // red and british
    for(int k = 1; k <= 5; ++k)
    {
        cout << "-" << lives(k, british) << " " << color(k, red) << " 0" << endl;
        cout << lives(k, british) << " -" << color(k, red) << " 0" << endl;
    }

    // swedish and dog
    for(int k = 1; k <= 5; ++k)
    {
        cout << "-" << lives(k, swedish) << " " << pets(k, dog) << " 0" << endl;
        cout << lives(k, swedish) << " -" << pets(k, dog) << " 0" << endl;
    }

    // blends and cat neighbor
    cout << "-" << cigars(1, blends) << " " << pets(2, cat) << " 0" << endl;
    cout << "-" << cigars(5, blends) << " " << pets(4, cat) << " 0" << endl;
    for(int k = 2; k <= 4; ++k)
    {
        cout << "-" << cigars(k, blends) << " " << pets(k-1, cat) << " " << pets(k+1, cat) << " 0" << endl;
    }

    return 0;
}
