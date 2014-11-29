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
    // House and Color
    for(int k = 0; k < 5; ++k)
    {
		// every house has a color
        for(int house = 1; house <= 5; ++house)
        {
             cout << color(house, k) << " ";
        }
        cout << "0" << endl;

		// use color only once
        for(int house = 1; house <= 5; ++house)
        {
            for(int house1 = 1; house1 < house; ++house1)
            {
                cout << "-" << color(house1,k) << " -" << color(house, k) << " 0" << endl;
            }
        }

	    // only one color per house
        for(int house = 1; house <= 5; ++house)
        {
            for(int k1 = 0; k1 < 5; ++k1)
            {
                if(k1 != k)
                {
                    cout << "-" << color(house,k) << " -" << color(house, k1) << " 0" << endl; 
                }
            }
		}
    } 

    // House and Drink
    for(int k = 10; k < 15; ++k)
    {
        for(int house = 1; house <= 5; ++house)
        {
             cout << drinks(house, k) << " "; // every person at a house drinks
        }
        cout << "0" << endl;

        for(int house = 1; house <= 5; ++house)
        {
            for(int house1 = 1; house1 < house; ++house1)
            {
                cout << "-" << drinks(house,k) << " -" << drinks(house1, k) << " 0" << endl; // use drink only once
            }
    
            for(int k1 = 10; k1 < 15; ++k1)
            {
                if(k1 != k)
                {
                    cout << "-" << drinks(house,k) << " -" << drinks(house, k1) << " 0" << endl; // only one drink per house
                }
            }
        }
    } 

    // House and Cigar
    for(int k = 15; k < 20; ++k)
    {
        for(int house = 1; house <= 5; ++house)
        {
             cout << cigars(house, k) << " "; // every person at a house smokes
        }
        cout << "0" << endl;

        for(int house = 1; house <= 5; ++house)
        {
            for(int house1 = 1; house1 < house; ++house1)
            {
                cout << "-" << cigars(house,k) << " -" << cigars(house1, k) << " 0" << endl; // use each cigar type only once
            }
    
            for(int k1 = 15; k1 < 20; ++k1)
            {
                if(k1 != k)
                {
                    cout << "-" << cigars(house,k) << " -" << cigars(house, k1) << " 0" << endl; // each person only smokes one type of cigar
                }
            }
        }
    } 

    // House and Pets
    for(int k = 20; k < 25; ++k)
    {
        for(int house = 1; house <= 5; ++house)
        {
             cout << pets(house, k) << " "; // every person has a pet
        }
        cout << "0" << endl;

        for(int house = 1; house <= 5; ++house)
        {
            for(int house1 = 1; house1 < house; ++house1)
            {
                cout << "-" << pets(house,k) << " -" << pets(house1, k) << " 0" << endl; // use each pet only once
            }
    
            for(int k1 = 20; k1 < 25; ++k1)
            {
                if(k1 != k)
                {
                    cout << "-" << pets(house,k) << " -" << pets(house, k1) << " 0" << endl; // each person only keeps one pet
                }
            }
        }
    } 

    // House and Nationality
    for(int k = 5; k < 10; ++k)
    {
        for(int house = 1; house <= 5; ++house)
        {
             cout << lives(house, k) << " "; // every person lives in a house
        }
        cout << "0" << endl;

        for(int house = 1; house <= 5; ++house)
        {
            for(int house1 = 1; house1 < house; ++house1)
            {
                cout << "-" << lives(house,k) << " -" << lives(house1, k) << " 0" << endl; // use each person nationality only once
            }
    
            for(int k1 = 5; k1 < 10; ++k1)
            {
                if(k1 != k)
                {
                    cout << "-" << lives(house,k) << " -" << lives(house, k1) << " 0" << endl; // each house only has one person
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

    // green and coffee
    for(int k = 1; k <= 5; ++k)
    {
        cout << "-" << color(k, green) << " " << drinks(k, coffee) << " 0" << endl;
        cout << color(k, green) << " -" << drinks(k, coffee) << " 0" << endl;
    }

    // danish and tea
    for(int k = 1; k <= 5; ++k)
    {
        cout << "-" << lives(k, danish) << " " << drinks(k, tea) << " 0" << endl;
        cout << lives(k, danish) << " -" << drinks(k, tea) << " 0" << endl;
    }

    // dunhill and yellow
    for(int k = 1; k <= 5; ++k)
    {
        cout << "-" << cigars(k, dunhill) << " " << color(k, yellow) << " 0" << endl;
        cout << cigars(k, dunhill) << " -" << color(k, yellow) << " 0" << endl;
    }

    // swedish and dog
    for(int k = 1; k <= 5; ++k)
    {
        cout << "-" << lives(k, swedish) << " " << pets(k, dog) << " 0" << endl;
        cout << lives(k, swedish) << " -" << pets(k, dog) << " 0" << endl;
    }

    // prince and german
    for(int k = 1; k <= 5; ++k)
    {
        cout << "-" << cigars(k, prince) << " " << lives(k, german) << " 0" << endl;
        cout << cigars(k, prince) << " -" << lives(k, german) << " 0" << endl;
    }

    // pallmall and bird
    for(int k = 1; k <= 5; ++k)
    {
        cout << "-" << cigars(k, pallmall) << " " << pets(k, bird) << " 0" << endl;
        cout << cigars(k, pallmall) << " -" << pets(k, bird) << " 0" << endl;
    }

    // bluemasters and beer
    for(int k = 1; k <= 5; ++k)
    {
        cout << "-" << cigars(k, bluemasters) << " " << drinks(k, beer) << " 0" << endl;
        cout << cigars(k, bluemasters) << " -" << drinks(k, beer) << " 0" << endl;
    }

    // horse and dunhill neighbor
    cout << "-" << pets(1, horse) << " " << cigars(2, dunhill) << " 0" << endl;
    cout << "-" << pets(5, horse) << " " << cigars(4, dunhill) << " 0" << endl;
    for(int k = 2; k <= 4; ++k)
    {
        cout << "-" << pets(k, horse) << " " << cigars(k-1, dunhill) << " " << cigars(k+1, dunhill) << " 0" << endl;
    }

    // blends and cat neighbor
    cout << "-" << cigars(1, blends) << " " << pets(2, cat) << " 0" << endl;
    cout << "-" << cigars(5, blends) << " " << pets(4, cat) << " 0" << endl;
    for(int k = 2; k <= 4; ++k)
    {
        cout << "-" << cigars(k, blends) << " " << pets(k-1, cat) << " " << pets(k+1, cat) << " 0" << endl;
    }

    // blends and water neighbor
    cout << "-" << cigars(1, blends) << " " << drinks(2, water) << " 0" << endl;
    cout << "-" << cigars(5, blends) << " " << drinks(4, water) << " 0" << endl;
    for(int k = 2; k <= 4; ++k)
    {
        cout << "-" << cigars(k, blends) << " " << drinks(k-1, water) << " " << drinks(k+1, water) << " 0" << endl;
    }

	// green to the left of white
	for(int w = 1; w <= 5; ++w)
	{
		for(int g = 5; g > 0; --g)
		{
			if(g < (w-1) || g > w)
			{
				cout << "-" << color(w, white) << " -" << color(g, green) << " 0" << endl;
			}
		}
	}

    return 0;
}
