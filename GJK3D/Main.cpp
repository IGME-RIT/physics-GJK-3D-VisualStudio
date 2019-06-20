/*
Title: GJK-3D (OBB)
File Name: Main.cpp
Copyright © 2015
Original authors: Brockton Roth
Modified by: Parth Contractor
Written under the supervision of David I. Schwartz, Ph.D., and
supported by a professional development seed grant from the B. Thomas
Golisano College of Computing & Information Sciences
(https://www.rit.edu/gccis) at the Rochester Institute of Technology.

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or (at
your option) any later version.

This program is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.

Description:
This is a Gilbert-Johnson-Keerthi test. (Called GJK for short.) This is in 3D.
Contains two cubes, one that is stationary and one that is moving. They are bounded
by OBBs (Object-Oriented Bounding Boxes) and when these OBBs collide the moving object
"bounces" on the x axis (because that is the only direction the object is moving).
The algorithm will detect any axis of collision, but will not output the axis that was
collided (because it doesn't know). Thus, we assume x and hardcode in the x axis bounce.
There is a physics timestep such that every update runs at the same delta time, regardless
of how fast or slow the computer is running. The cubes would be the exact same as their OBBs,
since they are aligned on the same axis.
*/

#include "GLIncludes.h"
#include "GLRender.h"
#include "GameObject.h"
#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <algorithm>

// Variables for FPS and Physics Timestep calculations.
int frame = 0;
double time = 0;
double timebase = 0;
double accumulator = 0.0;
int fps = 0;
double FPSTime = 0.0;
double physicsStep = 0.012; // This is the number of milliseconds we intend for the physics to update.

bool antiStuck = false;

// Reference to the window object being created by GLFW.
GLFWwindow* window;

struct OBB
{
	glm::vec3 corners[8];
};

OBB obb1;
OBB obb2;

std::vector<glm::vec3> simplex;

// Gets the farthest point of a given OBB in a given direction
glm::vec3 getFarthestPointInDirection(OBB obj, glm::vec3& dir)
{
	// Project the first point onto the direction and make it the farthestPoint.
	float maxDist = glm::dot(obj.corners[0], dir);
	glm::vec3 farthestPoint = obj.corners[0];

	for (int i = 1; i < 8; i++)
	{
		// Project point onto the direction, no need to divide by dir.length() as every point will have this same value, as it is an extra calculation
		// that is not necessary, since we don't need the exact scalar projection value, just the maximum.
		if (glm::dot(obj.corners[i], dir) > maxDist)
		{
			maxDist = glm::dot(obj.corners[i], dir);
			farthestPoint = obj.corners[i];
		}
	}

	return farthestPoint;
}

// Gets the farthest points in opposite directions for two OBBs and a given direction to project along, and then returns the difference between those points.
glm::vec3 Support(OBB a, OBB b, glm::vec3& dir)
{
	glm::vec3 negativeDir = -dir;

	glm::vec3 p1 = getFarthestPointInDirection(a, dir); // = a.getFarthestPointInDirection(dir)
	glm::vec3 p2 = getFarthestPointInDirection(b, negativeDir); // = b.getFarthestPointInDirection(-dir)

	glm::vec3 p3 = p1 - p2;

	return p3;
}

// Checks the tetrahedron for a proper value for dir and re-adjusts the simplex vector. (Returns false no matter what.)
bool checkTetrahedron(const glm::vec3& ao, const glm::vec3& ab, const glm::vec3& ac, const glm::vec3& abc, glm::vec3& dir)
{
	// simplex[0] = d, simplex[1] = c, simplex[2] = b, simplex[3] = a

	// Very similar to triangle checks
	glm::vec3 ab_abc = glm::cross(ab, abc);

	if (glm::dot(ab_abc, ao) > 0)
	{
		// Update our simplex vertices
		simplex[1] = simplex[2]; // c = b
		simplex[2] = simplex[3]; // b = a

		// The direction is not a_abc because it does not point toward the origin.
		dir = glm::cross(glm::cross(ab, ao), ab);

		// Erase d and a
		simplex.erase(simplex.begin());
		simplex.erase(simplex.end() - 1);

		return false;
	}

	glm::vec3 acp = glm::cross(abc, ac);

	if (glm::dot(acp, ao) > 0)
	{
		simplex[2] = simplex[3]; // b = a

		dir = glm::cross(glm::cross(ac, ao), ac);

		// Erase d and a
		simplex.erase(simplex.begin());
		simplex.erase(simplex.end() - 1);

		return false;
	}

	simplex[0] = simplex[1]; // d = c
	simplex[1] = simplex[2]; // c = b
	simplex[2] = simplex[3]; // b = a

	// Only erase a
	simplex.erase(simplex.end() - 1);

	dir = abc;

	return false;
}

// Tests if the global simplex contains the origin.
bool ContainsOrigin(glm::vec3& dir)
{
	glm::vec3 a = simplex.back(); // a will always equal the last value in the simplex
	glm::vec3 b, c, d, ab, ac, ad;

	// If we have a triangle.
	if (simplex.size() == 3)
	{
		// Setup up our b and c variables.
		b = simplex[1];
		c = simplex[0];

		// Calculate ab, ac
		ab = b - a;
		ac = c - a;

		// Create abc and ab_abc to test if the origin is away from the ab edge.
		glm::vec3 abc = glm::cross(ab, ac);
		glm::vec3 ab_abc = glm::cross(ab, abc);

		// If this is true, then ab_abc is not pointing toward the origin.
		if (glm::dot(ab_abc, -a) > 0)
		{
			// c's value is lost.
			simplex[0] = simplex[1]; // c = b
			simplex[1] = simplex[2]; // b = a

			// doubleCross(ab, -a)
			dir = glm::cross(glm::cross(ab, -a), ab); // The dir can't be ab_abc since it's in the wrong direction.

			// Remove a.
			simplex.erase(simplex.end() - 1);

			return false;
		}

		glm::vec3 abc_ac = glm::cross(abc, ac);

		if (glm::dot(abc_ac, -a) > 0)
		{
			simplex[1] = simplex[2]; // b = a

			// doubleCross(ac, -a)
			dir = glm::cross(glm::cross(ac, -a), ac);
			simplex.erase(simplex.end() - 1);

			return false;
		}

		// If we've made it this far, we still have 3 points.
		// simplex[0] = c, simplex[1] = b, simplex[2] = a
		// We wish to make a tetrahedron
		
		if (glm::dot(abc, -a) > 0)
		{
			// Leave simplex as-is
			// d = c, c = b, b = a (naturally done)
			// simplex[0] = d, simplex[1] = c, simplex[2] = b, simplex[3] = a (does not exist yet)
			dir = abc;
		}
		else
		{
			// Upside down tetrahedron
			// simplex[0] = d, simplex[1] = c, simplex[2] = b, simplex[3] = a (does not exist yet)
			glm::vec3 temp = simplex[1];
			simplex[1] = simplex[0]; // c = oldC
			simplex[0] = temp; // d = b
			// b = a (naturally done)

			dir = -abc;
		}

		return false;
	}
	else if (simplex.size() == 2)
	{
		// Line segment
		b = simplex[0];

		ab = b - a;
		
		// Triple product
		// doubleCross(ab, -a)
		dir = glm::cross(glm::cross(ab, -a), ab);

		// We still have 2 points
		// simplex[0] = b, simplex[1] = a
		// We wish to make a triangle such that:
		// simplex[0] = c, simplex[1] = b, simplex[2] = a
		// c = b, b = a (naturally done)

		return false;

		// ab, -a, ab
		//dir = (-a * glm::dot(ab, ab)) - (ab * glm::dot(ab, -a));
	}
	else if (simplex.size() == 4) // We have a tetrahedron
	{
		d = simplex[0];
		c = simplex[1];
		b = simplex[2];

		ab = b - a;
		ac = c - a;
		ad = d - a;

		// simplex[0] = d, simplex[1] = c, simplex[2] = b, simplex[3] = a

		glm::vec3 abc = glm::cross(ab, ac);

		if (glm::dot(abc, -a) > 0)
		{
			// This is in front of triangle ABC, so we don't have to change variables around.
			return checkTetrahedron(-a, ab, ac, abc, dir);
		}

		glm::vec3 acd = glm::cross(ac, ad);

		if (glm::dot(acd, -a) > 0)
		{
			// Since this is in front of triangle ACD

			// b value eliminated
			simplex[2] = simplex[1]; // b = c
			simplex[1] = simplex[0]; // c = d
			ab = ac;
			ac = ad;
			abc = acd;

			return checkTetrahedron(-a, ab, ac, abc, dir);
		}
		
		glm::vec3 adb = glm::cross(ad, ab);

		if (glm::dot(adb, -a) > 0)
		{
			// Since this is in front of triangle ADB

			// c value eliminated
			simplex[1] = simplex[2]; // c = b
			simplex[2] = simplex[0]; // b = d

			ac = ab;
			ab = ad;

			abc = adb;
			return checkTetrahedron(-a, ab, ac, abc, dir);
		}

		// If you made it this far and then you are overlapping the origin which means there is a collision!
		return true;
	}
	/*else // If you have something unexpected coming through here, maybe your simplex is too big or too small? Uncomment below and add a break statement.
	{
		std::cout << "ERROR";
	}*/

	return false;
}

bool TestGJK(OBB a, OBB b)
{
	simplex.clear();
	
	glm::vec3 dir = glm::vec3(1.0f);// a.corners[0] - b.corners[1]; // Choose a start direction

	simplex.push_back(Support(a, b, dir)); // c

	dir = -simplex.back(); // -c

	simplex.push_back(Support(a, b, dir)); // b

	if (glm::dot(simplex.back(), dir) < 0)
	{
		return false;
	}

	dir = glm::cross(glm::cross(simplex[0] - simplex[1], -simplex[1]), simplex[0] - simplex[1]);


	while (true)
	{
		simplex.push_back(Support(a, b, dir)); // a

		if (glm::dot(simplex.back(), dir) <= 0)
		{
			// Sometimes you get unexpected values, so uncommenting below and putting a break statement can help you debug what might throw a zero in your dot product.
			/*if (glm::dot(simplex.back(), dir) == 0)
			{
				return false;
			}*/


			// If the point added last was not past the origin in the direction of d, then the Minkowski Sum cannot contain the origin since the last 
			// point added is on the edge of the Minkowski Difference.
			return false;
		}
		else
		{
			if (ContainsOrigin(dir))
			{
				return true;
			}
		}
	}
}

// This runs once every physics timestep.
void update(float dt)
{
#pragma region Boundaries
	// This section just checks to make sure the object stays within a certain boundary. This is not really collision detection.
	glm::vec3 tempPos = obj2->GetPosition();
	
	if (fabsf(tempPos.x) > 1.35f)
	{
		glm::vec3 tempVel = obj2->GetVelocity();

		// "Bounce" the velocity along the axis that was over-extended.
		obj2->SetVelocity(glm::vec3(-1.0f * tempVel.x, tempVel.y, tempVel.z));
	}
	if (fabsf(tempPos.y) > 0.8f)
	{
		glm::vec3 tempVel = obj2->GetVelocity();
		obj2->SetVelocity(glm::vec3(tempVel.x, -1.0f * tempVel.y, tempVel.z));
	}
	if (fabsf(tempPos.z) > 1.0f)
	{
		glm::vec3 tempVel = obj2->GetVelocity();
		obj2->SetVelocity(glm::vec3(tempVel.x, tempVel.y, -1.0f * tempVel.z));
	}
#pragma endregion Boundaries section just bounces the object so it does not fly off the side of the screen infinitely.

	// Rotate the objects. This helps illustrate how the OBB follows the object's orientation.
	 obj1->Rotate(glm::vec3(glm::radians(1.0f), glm::radians(1.0f), glm::radians(0.0f)));
	 obj2->Rotate(glm::vec3(glm::radians(1.0f), glm::radians(1.0f), glm::radians(0.0f)));

	// Re-calculate the Object-Oriented Bounding Box for your object.
	// We do this because if the object's orientation changes, we should update the bounding box as well.
	// Be warned: For some objects this can actually cause a collision to be missed, so be careful.
	// (This is because we determine the collision based on the OBB, but if the OBB changes significantly, the time of collision can change between frames,
	// and if that lines up just right you'll miss the collision altogether.)
	 glm::vec4 pointsA[8];
	 glm::vec4 pointsB[8];

	 for (int i = 0; i < 8; i++)
	 {
		 pointsA[i] = *obj1->GetTransform() * glm::vec4(obj1->GetModel()->Vertices()[i].position, 1.0f);
		 pointsB[i] = *obj2->GetTransform() * glm::vec4(obj2->GetModel()->Vertices()[i].position, 1.0f);

		 obb1.corners[i] = glm::vec3(pointsA[i].x, pointsA[i].y, pointsA[i].z);
		 obb2.corners[i] = glm::vec3(pointsB[i].x, pointsB[i].y, pointsB[i].z);
	 }

	// Pass in our two objects to the GJK test, if it returns true then they are colliding because the Minkowski Sum (Difference) contains the origin.
	 if (TestGJK(obb2, obb1) && !antiStuck)
	{
		glm::vec3 velocity = obj2->GetVelocity();
		
		// Reverse the velocity in the x direction
		// This is the "bounce" effect, only we don't actually know the axis of collision from the test. Instead, we assume it because the object is only moving in the x 
		// direction.
		velocity.x *= -1;

		obj2->SetVelocity(velocity);

		// This variable exists to allow an extra frame/update to pass when they collide so that the objects do not get stuck as a result of tunneling and 
		// recalculating the OBB.
		antiStuck = true;
	}
	else if (antiStuck)
	{
		antiStuck = false;
	}
	
	// Update the objects based on their velocities.
	obj1->Update(dt);
	obj2->Update(dt);

	// Update your MVP matrices based on the objects' transforms.
	MVP = PV * *obj1->GetTransform();
	MVP2 = PV * *obj2->GetTransform();
}

// This runs once every frame to determine the FPS and how often to call update based on the physics step.
void checkTime()
{
	// Get the current time.
	time = glfwGetTime();

	// Get the time since we last ran an update.
	double dt = time - timebase;

	// If more time has passed than our physics timestep.
	if (dt > physicsStep)
	{
		// Calculate FPS: Take the number of frames (frame) since the last time we calculated FPS, and divide by the amount of time that has passed since the 
		// last time we calculated FPS (time - FPSTime).
		if (time - FPSTime > 1.0)
		{
			fps = frame / (time - FPSTime);

			FPSTime = time; // Now we set FPSTime = time, so that we have a reference for when we calculated the FPS
			
			frame = 0; // Reset our frame counter to 0, to mark that 0 frames have passed since we calculated FPS (since we literally just did it)

			std::string s = "FPS: " + std::to_string(fps); // This just creates a string that looks like "FPS: 60" or however much.

			glfwSetWindowTitle(window, s.c_str()); // This will set the window title to that string, displaying the FPS as the window title.
		}

		timebase = time; // Set timebase = time so we have a reference for when we ran the last physics timestep.

		// Limit dt so that we if we experience any sort of delay in processing power or the window is resizing/moving or anything, it doesn't update a bunch of times while the player can't see.
		// This will limit it to a .25 seconds.
		if (dt > 0.25)
		{
			dt = 0.25;
		}

		// The accumulator is here so that we can track the amount of time that needs to be updated based on dt, but not actually update at dt intervals and instead use our physicsStep.
		accumulator += dt;

		// Run a while loop, that runs update(physicsStep) until the accumulator no longer has any time left in it (or the time left is less than physicsStep, at which point it save that 
		// leftover time and use it in the next checkTime() call.
		while (accumulator >= physicsStep)
		{
			update(physicsStep);

			accumulator -= physicsStep;
		}
	}
}



int main(int argc, char **argv)
{
	// Initializes the GLFW library
	glfwInit();

	// Creates a window given (width, height, title, monitorPtr, windowPtr).
	// Don't worry about the last two, as they have to do with controlling which monitor to display on and having a reference to other windows. Leaving them as nullptr is fine.
	window = glfwCreateWindow(800, 600, "GJK 3D Collision", nullptr, nullptr);

	// Makes the OpenGL context current for the created window.
	glfwMakeContextCurrent(window);
	
	// Sets the number of screen updates to wait before swapping the buffers.
	// Setting this to zero will disable VSync, which allows us to actually get a read on our FPS. Otherwise we'd be consistently getting 60FPS or lower, 
	// since it would match our FPS to the screen refresh rate.
	// Set to 1 to enable VSync.
	glfwSwapInterval(0);

	// Initializes most things needed before the main loop
	init();

	// Enter the main loop.
	while (!glfwWindowShouldClose(window))
	{
		// Call to checkTime() which will determine how to go about updating via a set physics timestep as well as calculating FPS.
		checkTime();

		// Call the render function.
		renderScene();

		// Swaps the back buffer to the front buffer
		// Remember, you're rendering to the back buffer, then once rendering is complete, you're moving the back buffer to the front so it can be displayed.
		glfwSwapBuffers(window);

		// Add one to our frame counter, since we've successfully 
		frame++;

		// Checks to see if any events are pending and then processes them.
		glfwPollEvents();
	}

	cleanup();

	return 0;
}